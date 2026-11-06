(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain of the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of
   fuzz_reply's LLVMFuzzerTestOneInput - the jump table's arm 2 (op_drain), SECOND STAGE: the six calls, from
   `jal pthread_mutex_lock` (0x84900, the state DLK of lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v) to the arm's
   exit `j 84804` into the latch.  Proves no function (kind: segment walk - a segment of the entry function, its
   six callees taken as named contracts).

   Image: the pinned asan-ubsan objdump of fuzz_reply (fuzz_reply.objdump.txt sha256 17f5c434bf57; internal record),
   sha256 17f5c434bf5755fb1ceaed0ac3e631e85a2eae980ed9983d0ee03955bf5307ac.

   ------------------------------------------------------------------ the stretch this file walks (B's own code)
     0x848f4  auipc a0,0x554 ; addi s7,a0,1868      s7 = &g_lock (0x5d9040)          [stage 1's tail]
     0x848fc  mv a0,s7 ; jal 98dbc <pthread_mutex_lock>            ra = 0x84904 = BASE + A_dr_r1
     0x84904  mv a0,s6 ; jal 83278 <drain>                         ra = 0x8490c = BASE + A_dr_r2
     0x8490c  mv a0,s7 ; li s7,1 ; jal 992a8 <pthread_mutex_unlock> ra = 0x84918 = BASE + A_dr_r3
     0x84918  mv a0,s5 ; jal 85dd4 <check_no_loss_read>            ra = 0x84920 = BASE + A_dr_r4
     0x84920  addi a1,s1,192 ; mv a0,s5 ; jal 85e3c <check_no_loss> ra = 0x8492c = BASE + A_dr_r5
     0x8492c  ld a0,192(s1) ; jal 85a5c <check_shape_done>         ra = 0x84934 = BASE + A_dr_r6
     0x84934  j 84804                                              the latch, AF_LLVM_latch
   NO TRAP BRANCH lies on this stretch (the arm's three UBSan traps 0x8489c, 0x848a4, 0x848d4 are all in stage 1),
   so no `trap_<shape>` lemma of lib/B/W_traps.v is cited here and the runner decides every branch it meets.

   ------------------------------------------------------------------ what this walk carries, and B's differences
   from image A's twin lib/A/W_LLVMFuzzerTestOneInput_drain.v (a86c2788a94, dc_stA..dc_stF / dc_calls), whose
   structure this file ports:
     - &g_lock lives in s7 (reg 23), not in the frame cell F+40: dc_regs carries `getr regs 23 = w64 s7v` with
       s7v = rg_lock fr_RG before 0x84910 and s7v = 1 after it (`li s7,1`), which is what lregs_common asks of
       reg 23 at the latch.  There is no `sv8 (F+40) (rg_lock fr_RG)` conjunct anywhere.
     - B's aframe_at has no `full` flag, and lcut carries one more conjunct, `sv8 W mem (FF + 120)
       (flag_addr ly 1 fpos)`, a byte range of the owned class-1 fake frame: it rides the same keeper as the fake
       frame's 128 bytes.
     - the arm has no join block: 0x84934 jumps straight to the latch, s9 (= t, reg 25) and s4 (= the cursor,
       reg 20) are never reloaded, so dc_stF lands on INV_K itself.
     - check_no_loss is the kit's cnl_spec, lib/B/W_contract.v:2054 (cnl_post :1967, CNL_STK :1966 = 16640,
       Section w3n), taken at G = [(HA + 64, 32)], the drained slot's two list headers.
     - drain's aothers_at compares the fds modulo 2 ^ 32 (lib/B/W_contract.v:969, the machine's `beq a1,a4`),
       where image A compares them outright.
     - ablocks_sep's second clause is over the block's REQUEST size already (lib/B/W_LLVMFuzzerTestOneInput_cut.v
       :412-416), so no widening step (image A's FP_REQ) appears at the two calls that name a footprint.

   Every address, frame cell, register, global and shadow fact below is B's own.  The interface this file builds
   on is lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v (the arm's addresses, DLK, dr_env and the model notions);
   the arm's first stage (0x8489c-0x84900) and the closing file are other lanes'. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* Every lemma below is discharged over the WHOLE Section context, so that the closing file applies each of them
   with the Section header's variables in their declaration order (B MT XM_LIB XN_LIB RLO RHI fr_live_pre
   fr_live_post fr_surv G_fr fr_FP LAWS HG LS RINV MMAX EV). *)
Set Default Proof Using "All".

(* ------------------------------------------------------------------ the model side: plain lists and records *)
(* the stream's control state with errno re-read: every callee below but drain leaves errno where it found it, and
   drain's own post fixes the other four flags, so the arm carries the value as a parameter *)
Definition dc_ctl (c : ctl) (ev : Z) : ctl := CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) ev.
Lemma dc_ctl_eta : forall c, dc_ctl c (ct_ev c) = c.
Proof. intros [cl br dd ei ev]. reflexivity. Qed.
Lemma dc_ctl_dr : forall c h ev' ev, dc_ctl (dr_ctl c h ev') ev = dr_ctl c h ev.
Proof. intros c h ev' ev. reflexivity. Qed.
Lemma dc_set_nth_twice : forall (A : Type) n (x y : A) l, set_nth n x (set_nth n y l) = set_nth n x l.
Proof.
  intros A n. induction n as [|n IH]; intros x y [|z l]; cbn [set_nth]; try reflexivity. f_equal. apply IH.
Qed.
(* the drain's functional half (dr_step_ok's first part) and check_no_loss's (its second part) *)
Definition dr_dfun (m : lmod) (si : nat) (h : hsrc) (j : nat) (e' : rentry) (h' : hsrc) (LB : list byte) : Prop :=
  let e := nth j (lm_es m) dr_e0 in
  let fin := dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) e h in
  re_fd e' = re_fd e /\ re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\ 0 < re_cap e' /\
  re_cap e' = drain_b_c.ds_cap fin /\ bzs (re_U e') = drain_b_c.ds_u fin /\
  re_skip e' = (if drain_b_c.ds_skip fin then 1 else 0) /\
  drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
  NoDup (drain_b_c.keys_texts (re_keys e')) /\
  same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
  hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
  hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
  hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
  map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
  hs_held h' = hs_held h /\
  re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
  bzs LB = with_nul (dr_lines h) /\
  hl_cap (hs_expected h') = drain_b_c.ds_ecap fin.
Definition dr_cfun (h' : hsrc) (E' H' : hlist) : Prop :=
  hl_recs E' = [] /\ hl_v E' = hl_v (hs_expected h') /\ hl_cap E' = hl_cap (hs_expected h') /\
  NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h')) (texts (hs_expected h')).
(* the stream and the controller's buffer after the drain, and the model after it (in.k not yet advanced) *)
Definition dr_O1 (m : lmod) (h : hsrc) (LB : list byte) : list byte :=
  if dr_live (lm_c m) h then lm_O m ++ LB else lm_O m.
Definition dr_cap1 (m : lmod) (j : nat) (h : hsrc) : Z :=
  if dr_live (lm_c m) h
  then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
  else lm_cap m.
Definition dr_m1 (m : lmod) (j si : nat) (h h' : hsrc) (e' : rentry) (ev' : Z) (LB : list byte) (out' : Z) : lmod :=
  dr_step m (lm_k m) si h' j e' (dr_ctl (lm_c m) h ev') (dr_O1 m h LB) (dr_cap1 m j h) out'.
Definition dc_setsrc (mc : lmod) (si : nat) (h : hsrc) : lmod :=
  LM (lm_k mc) (set_nth si (Some h) (lm_hs mc)) (lm_G mc) (lm_es mc) (lm_c mc) (lm_O mc) (lm_mx mc) (lm_cap mc)
     (lm_out mc) (lm_gn mc) (lm_nfd mc).

(* ---- the pure list facts the two block arguments run on ---- *)
Lemma dc_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma dc_cnt_cons : forall g l x,
  count_occ dc_dec (g :: l) x = ((if dc_dec g x then 1 else 0) + count_occ dc_dec l x)%nat.
Proof. intros g l x. cbn [count_occ]. destruct (dc_dec g x); reflexivity. Qed.
Ltac dc_perm := apply (Permutation_count_occ dc_dec); intros ?x;
  repeat first [rewrite count_occ_app | rewrite dc_cnt_cons]; lia.
Lemma dra_split : forall (A : Type) (l : list A) (j : nat) (d : A),
  (j < length l)%nat -> l = firstn j l ++ nth j l d :: skipn (S j) l.
Proof.
  intros A l. induction l as [|a l IH]; intros [|j] d Hj; cbn [length] in Hj.
  - lia.
  - lia.
  - reflexivity.
  - cbn [firstn nth skipn app]. f_equal. apply IH. lia.
Qed.
Lemma dra_set_nth_split : forall (A : Type) (l : list A) (j : nat) (x : A),
  (j < length l)%nat -> set_nth j x l = firstn j l ++ x :: skipn (S j) l.
Proof.
  intros A l. induction l as [|a l IH]; intros [|j] x Hj; cbn [length] in Hj.
  - lia.
  - lia.
  - reflexivity.
  - cbn [set_nth firstn skipn app]. f_equal. apply IH. lia.
Qed.
Lemma dra_concat_split : forall (A C : Type) (f : A -> list C) (l : list A) (j : nat) (d : A),
  (j < length l)%nat ->
  concat (map f l) = concat (map f (firstn j l)) ++ f (nth j l d) ++ concat (map f (skipn (S j) l)).
Proof.
  intros A C f l j d Hj. rewrite (dra_split A l j d Hj) at 1. rewrite map_app, concat_app. reflexivity.
Qed.
Lemma dra_concat_set_split : forall (A C : Type) (f : A -> list C) (l : list A) (j : nat) (x : A),
  (j < length l)%nat ->
  concat (map f (set_nth j x l)) = concat (map f (firstn j l)) ++ f x ++ concat (map f (skipn (S j) l)).
Proof.
  intros A C f l j x Hj. rewrite (dra_set_nth_split A l j x Hj). rewrite map_app, concat_app. reflexivity.
Qed.
Lemma dr_concat_nth_perm : forall (A C : Type) (f : A -> list C) (l : list A) (j : nat) (d : A),
  (j < length l)%nat ->
  Permutation (concat (map f l)) (f (nth j l d) ++ concat (map f (firstn j l ++ skipn (S j) l))).
Proof.
  intros A C f l j d Hj. rewrite (dra_concat_split A C f l j d Hj), map_app, concat_app, !app_assoc.
  apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma dr_concat_set_nth_perm : forall (A C : Type) (f : A -> list C) (l : list A) (j : nat) (x : A),
  (j < length l)%nat ->
  Permutation (concat (map f (set_nth j x l))) (f x ++ concat (map f (firstn j l ++ skipn (S j) l))).
Proof.
  intros A C f l j x Hj. rewrite (dra_concat_set_split A C f l j x Hj), map_app, concat_app, !app_assoc.
  apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma dr_map_set_nth : forall (A C : Type) (f : A -> C) (j : nat) (x : A) (l : list A),
  map f (set_nth j x l) = set_nth j (f x) (map f l).
Proof.
  intros A C f j x l. revert j. induction l as [|a l IH]; intros [|j]; cbn [set_nth map]; try reflexivity.
  f_equal. apply IH.
Qed.
Lemma dr_in_set_nth : forall (A : Type) (j : nat) (x y : A) (l : list A),
  In y (set_nth j x l) -> y = x \/ In y (firstn j l ++ skipn (S j) l).
Proof.
  intros A j x y l. revert j. induction l as [|a l IH]; intros [|j] H; cbn [set_nth firstn skipn app In] in H |- *.
  - destruct H.
  - destruct H.
  - destruct H as [E|H]; [left; symmetry; exact E | right; exact H].
  - destruct H as [E|H]; [right; left; exact E|].
    destruct (IH j H) as [E|H']; [left; exact E | right; right; exact H'].
Qed.
Lemma dr_in_rm : forall (A : Type) (j : nat) (y : A) (l : list A),
  In y (firstn j l ++ skipn (S j) l) -> In y l.
Proof.
  intros A j y l H. apply in_app_or in H. destruct H as [H|H].
  - rewrite <- (firstn_skipn j l). apply in_or_app. left. exact H.
  - rewrite <- (firstn_skipn (S j) l). apply in_or_app. right. exact H.
Qed.
Lemma dra_len_split : forall (A : Type) (l : list A) (j : nat), (j < length l)%nat ->
  length (firstn j l) = j /\ length (skipn (S j) l) = (length l - S j)%nat.
Proof.
  intros A l. induction l as [|a l IH]; intros [|j] Hj; cbn [length firstn skipn] in Hj |- *.
  - lia.
  - lia.
  - split; [reflexivity | change (skipn 0 l) with l; lia].
  - destruct (IH j ltac:(lia)) as [H1 H2]. split; lia.
Qed.
Lemma dra_Forall_firstn : forall (A : Type) (P : A -> Prop) (j : nat) (l : list A), Forall P l -> Forall P (firstn j l).
Proof. intros A P j l H. rewrite <- (firstn_skipn j l) in H. apply Forall_app in H. exact (proj1 H). Qed.
Lemma dra_Forall_skipn : forall (A : Type) (P : A -> Prop) (j : nat) (l : list A), Forall P l -> Forall P (skipn j l).
Proof. intros A P j l H. rewrite <- (firstn_skipn j l) in H. apply Forall_app in H. exact (proj2 H). Qed.
Lemma dra_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.
Lemma dra_bzs_length : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma dra_concat_text_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, IH.
  replace (length (text_rec r)) with 16%nat by (unfold text_rec; rewrite length_app; reflexivity). cbn [length]. lia.
Qed.
Lemma dra_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8. cbn [length]. lia.
Qed.
(* With 4-byte paddings a source_t is 56 bytes. *)
Lemma entry_bytes_length : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes.
  rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.
Lemma concat_entry_length : forall es,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  induction es as [|e es IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat length]. rewrite length_app, entry_bytes_length, IH by assumption. lia.
Qed.
Lemma nth_bzs : forall l n, nth n (bzs l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  unfold bzs. induction l as [|b l IH]; intros [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.
Lemma dc_lb1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. exact Hv.
Qed.
Lemma dc_bzs_inj : forall l1 l2, bzs l1 = bzs l2 -> l1 = l2.
Proof.
  induction l1 as [|b l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
(* the stream of the expected lines the drain appended is the bytes it relayed *)
Lemma dc_bstream_LB : forall (E : hlist) (L : list (list Z)) (LB : list byte),
  map snd (hl_recs E) = map (map (Z_to_bv 8)) L -> bzs LB = with_nul L -> bstream E = LB.
Proof.
  intros E L LB HM HB. apply dc_bzs_inj. rewrite HB. unfold bstream, with_nul.
  assert (HR : Forall (fun l => Forall (fun z => 0 <= z < 256) l) L).
  { assert (HZ : Forall (fun z => 0 <= z < 256) (with_nul L)).
    { rewrite <- HB. unfold bzs. apply Forall_map. apply Forall_forall. intros b _. unfold bz.
      pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. exact Hr. }
    unfold with_nul in HZ. clear - HZ. induction L as [|l L IH]; [constructor|].
    cbn [map concat] in HZ. apply Forall_app in HZ as [H1 H2]. apply Forall_app in H1 as [H1 _].
    constructor; [exact H1 | exact (IH H2)]. }
  replace (map (fun r : Z * list byte => snd r ++ [Z_to_bv 8 0]) (hl_recs E))
    with (map (fun l => l ++ [Z_to_bv 8 0]) (map snd (hl_recs E))) by (rewrite map_map; reflexivity).
  rewrite HM. clear HM HB. induction L as [|l L IH]; [reflexivity|].
  inversion HR as [|l0 L0 Hl HL]; subst. cbn [map concat]. unfold bzs in *. rewrite !map_app.
  rewrite IH by exact HL. f_equal. f_equal. rewrite map_map.
  rewrite <- (map_id l) at 2. apply map_ext_in. intros z Hz. rewrite Forall_forall in Hl.
  unfold bz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. exact (Hl z Hz).
Qed.
Lemma dc_LB_len : forall (LB : list byte) L, bzs LB = with_nul L -> Z.of_nat (length LB) = Z.of_nat (length (with_nul L)).
Proof. intros LB L H. rewrite <- H. unfold bzs. rewrite length_map. reflexivity. Qed.
(* permutations of block lists, by counting occurrences *)
Lemma dcB_perm_pre : forall (L I CA CS OB R0 ea hb CA' CS' : list (Z * Z)) g,
  Permutation L (I ++ (g :: CA ++ CS ++ OB) ++ R0) ->
  Permutation CA (ea ++ CA') -> Permutation CS (hb ++ CS') ->
  Permutation L (g :: ea ++ hb ++ OB ++ (CA' ++ CS' ++ I ++ R0)).
Proof. intros L I CA CS OB R0 ea hb CA' CS' g H HA HS. rewrite H, HA, HS. dc_perm. Qed.
Lemma dcB_perm_rest : forall (L ea hb ob T rest : list (Z * Z)) g,
  Permutation L (g :: ea ++ hb ++ ob ++ T) -> Permutation L (ea ++ hb ++ ob ++ rest) ->
  Permutation rest (g :: T).
Proof.
  intros L ea hb ob T rest g H1 H2. apply (Permutation_app_inv_l (ea ++ hb ++ ob)).
  transitivity L; [rewrite <- !app_assoc; symmetry; exact H2|].
  rewrite H1. dc_perm.
Qed.
Lemma dcB_perm_post : forall (L2 I R0 CA2 CS2 OB' ea' hb' CA' CS' rest : list (Z * Z)) g,
  Permutation L2 (ea' ++ hb' ++ OB' ++ rest) -> Permutation rest (g :: CA' ++ CS' ++ I ++ R0) ->
  Permutation CA2 (ea' ++ CA') -> Permutation CS2 (hb' ++ CS') ->
  Permutation L2 (I ++ (g :: CA2 ++ CS2 ++ OB') ++ R0).
Proof. intros L2 I R0 CA2 CS2 OB' ea' hb' CA' CS' rest g H1 H2 H3 H4. rewrite H1, H2, H3, H4. dc_perm. Qed.
Lemma dcE_perm_shape : forall (IB GE ENT OTH AO RS PP LE LH CS : list (Z * Z)),
  Permutation CS ((PP ++ LE ++ LH) ++ OTH) ->
  Permutation (IB ++ (GE ++ ENT ++ CS ++ AO) ++ RS) ((LE ++ LH) ++ PP ++ IB ++ GE ++ ENT ++ OTH ++ AO ++ RS).
Proof.
  intros IB GE ENT OTH AO RS PP LE LH CS HP.
  rewrite (Permutation_count_occ dc_dec) in HP |- *. intros x. specialize (HP x).
  rewrite !count_occ_app in HP. rewrite !count_occ_app. lia.
Qed.
Lemma dc_nd_app : forall (X R : list (Z * Z)) b, List.NoDup (X ++ R) -> In b X -> In b R -> False.
Proof.
  induction X as [|x X IH]; intros R b Hnd Hx Hr; [destruct Hx|].
  inversion Hnd as [|y l Hni Hnd' Heq]; subst.
  destruct Hx as [<- | Hx]; [apply Hni; apply in_or_app; right; exact Hr | exact (IH R b Hnd' Hx Hr)].
Qed.
Lemma dc_nd_r : forall (X R : list (Z * Z)), List.NoDup (X ++ R) -> List.NoDup R.
Proof. induction X as [|x X IH]; intros R H; [exact H|]. inversion H; subst. apply IH. assumption. Qed.
Lemma dcB_in_rest : forall (L X rest : list (Z * Z)) b, List.NoDup L -> Permutation L (X ++ rest) -> In b rest ->
  ~ In b X /\ In b L.
Proof.
  intros L X rest b Hnd HP Hb. split.
  - intros Hx. exact (dc_nd_app X rest b (Permutation_NoDup HP Hnd) Hx Hb).
  - apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hb.
Qed.
Lemma dcB_T_ne : forall (L X rest T : list (Z * Z)) g b, List.NoDup L -> Permutation L (X ++ rest) ->
  Permutation rest (g :: T) -> In b T -> b <> g.
Proof.
  intros L X rest T g b Hnd HP HR Hb ->.
  pose proof (dc_nd_r X rest (Permutation_NoDup HP Hnd)) as H1.
  pose proof (Permutation_NoDup HR H1) as H2. inversion H2 as [|y l Hni _]; subst. exact (Hni Hb).
Qed.
Lemma dc_in_rm_nth : forall (A : Type) (l : list A) (i j : nat) (d : A), (i < length l)%nat -> i <> j ->
  In (nth i l d) (firstn j l ++ skipn (S j) l).
Proof.
  intros A l. induction l as [|x l IH]; intros i j d Hi Hne; cbn [length] in Hi; [lia|].
  destruct i as [|i], j as [|j].
  - lia.
  - cbn [nth firstn skipn app]. left. reflexivity.
  - cbn [nth firstn skipn app]. change (skipn 0 l) with l. apply nth_In. lia.
  - cbn [nth firstn skipn app]. right. apply IH; lia.
Qed.
Lemma dcB_set_nth_nth : forall (A : Type) (l : list A) n d, set_nth n (nth n l d) l = l.
Proof. intros A l. induction l as [|x l IH]; intros [|n] d; cbn [set_nth nth]; try reflexivity. f_equal. apply IH. Qed.
Lemma dcE_inG1 : forall x n a, inG [(x, n)] a <-> x <= a < x + n.
Proof.
  intros x n a. unfold inG. split; intros H.
  - inversion H as [r l Hr Hl | r l Hr Hl]; subst; [unfold in_zr in Hr; cbn [fst snd] in Hr; lia | inversion Hr].
  - constructor. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma dcE_inG_mem : forall G x n a, In (x, n) G -> x <= a < x + n -> inG G a.
Proof. intros G x n a Hin Ha. unfold inG. apply Exists_exists. exists (x, n). split; [exact Hin | unfold in_zr; cbn; lia]. Qed.

(* the cut's own Local Notation, which does not leave its file (lib/B/W_LLVMFuzzerTestOneInput_cut.v:161) *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

Section dr.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable MMAX : Z.
Variable EV : dr_env B MT G_fr LS RINV MMAX.

(* ------------------------------------------------------------------ what the other lanes owe, by name
   (the fields of the arm's interface record, lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v dr_env) *)
#[local] Notation TL := (dre_TL B MT G_fr LS RINV MMAX EV).
#[local] Notation DRAIN := (dre_DRAIN B MT G_fr LS RINV MMAX EV).
#[local] Notation ALOCK := (dre_ALOCK B MT G_fr LS RINV MMAX EV).
#[local] Notation AUNLOCK := (dre_AUNLOCK B MT G_fr LS RINV MMAX EV).
#[local] Notation CNLR := (dre_CNLR B MT G_fr LS RINV MMAX EV).
#[local] Notation CSD := (dre_CSD B MT G_fr LS RINV MMAX EV).
#[local] Notation CNL := (dre_CNL B MT G_fr LS RINV MMAX EV).
#[local] Notation HGs := (dre_HGs B MT G_fr LS RINV MMAX EV).
#[local] Notation HG_DR := (dre_HG_DR B MT G_fr LS RINV MMAX EV).
#[local] Notation HGlock := (dre_HGlock B MT G_fr LS RINV MMAX EV).
#[local] Notation HG_GK := (dre_HG_GK B MT G_fr LS RINV MMAX EV).
#[local] Notation HERR_HI := (dre_HERR_HI B MT G_fr LS RINV MMAX EV).
#[local] Notation ERR := (dre_ERR B MT G_fr LS RINV MMAX EV).
#[local] Notation GWR := (dre_GWR B MT G_fr LS RINV MMAX EV).
#[local] Notation DR_ROM_OUT := (dre_ROM_OUT B MT G_fr LS RINV MMAX EV).
#[local] Notation HZS := (dre_HZS B MT G_fr LS RINV MMAX EV).
#[local] Notation HAP := (dre_HAP B MT G_fr LS RINV MMAX EV).
#[local] Notation RI_drain_step := (dre_RI_drain_step B MT G_fr LS RINV MMAX EV).
#[local] Notation RI_src := (dre_RI_src B MT G_fr LS RINV MMAX EV).
#[local] Notation RI_fds := (dre_RI_fds B MT G_fr LS RINV MMAX EV).
#[local] Notation RI_pair := (dre_RI_pair B MT G_fr LS RINV MMAX EV).
#[local] Notation RI_gone := (dre_RI_gone B MT G_fr LS RINV MMAX EV).
#[local] Notation LS_drain_pre := (dre_LS_drain_pre B MT G_fr LS RINV MMAX EV).
#[local] Notation LS_cnl_pre := (dre_LS_cnl_pre B MT G_fr LS RINV MMAX EV).
#[local] Notation LS_drain_step := (dre_LS_drain_step B MT G_fr LS RINV MMAX EV).

(* the walk's runners.  No trap branch lies on this stretch (the arm's three are all in stage 1), so every branch
   the runner meets it decides itself. *)
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].

(* the model the arm leaves at the latch: the drained model, with the cursor advanced and errno re-read *)
Definition dc_fin (cx : lfcx) (m mc : lmod) (ev : Z) : lmod :=
  LM (dr_k' cx m) (lm_hs mc) (lm_G mc) (lm_es mc) (dc_ctl (lm_c mc) ev) (lm_O mc) (lm_mx mc) (lm_cap mc)
     (lm_out mc) (lm_gn mc) (lm_nfd mc).

(* ------------------------------------------------------------------ the transport kit (image A's dr_ / dj_ /
   dt_ blocks, at B's registers and globals) *)
Definition DR_CEIL8 : Z := alloc_ceiling + 8.
Lemma dr_ceil_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof. pose proof asan_consts as (C1 & _). lia. Qed.
(* a live block: 4096 <= p, its request size under the ceiling *)
Lemma dr_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
Lemma dr_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
(* the image's membership is decidable *)
Lemma dj_in_img_dec : forall a, in_img segs a \/ ~ in_img segs a.
Proof.
  intros a. unfold in_img.
  destruct (existsb (fun sg => (Z.of_N (seg_base sg) <=? a) && (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs)
    eqn:Eb.
  - left. apply existsb_exists in Eb as (sg & Hs & Hb). apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists sg. split; [exact Hs | lia].
  - right. intros (sg & Hs & Hr). assert (Hx : existsb (fun sg => (Z.of_N (seg_base sg) <=? a) &&
      (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs = true).
    { apply existsb_exists. exists sg. split; [exact Hs|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite Hx in Eb. discriminate.
Qed.
(* a byte whose ASan view is kept is kept (writable_at reads the memory only at the byte) *)
Lemma dj_bk : forall (W W' : world segs) mem mem' a, 0 <= a < 2 ^ 64 -> (in_img segs a -> inG G_fr a) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Hr Hg Ha. split; [exact Ha|]. intros Hw.
  destruct (dj_in_img_dec a) as [Hi | Hi]; [exact (GWR _ _ a (Hg Hi))|].
  pose proof (mbyte_of_aview segs (w_H W) (w_H W') mem mem' a Ha) as Hm. unfold mbyte in Hm.
  rewrite (seg_rom_none segs a Hr Hi) in Hm.
  unfold writable_at, wview, arm in *.
  destruct (mrestrict (w_H W') mem' (Z_to_bv 64 a)) eqn:E1, (mrestrict (w_H W) mem (Z_to_bv 64 a)) eqn:E2;
    try discriminate; try exact Hw; try (intros X; discriminate X).
Qed.
(* what a callee's journal keeps, outside its G *)
Lemma dj_keep : forall G XO OUT STK sp FP ly S (W : world segs) mem md own ly' S' (W' : world segs) mem' md' k a,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
  0 <= a < 2 ^ 64 -> ~ inG G a ->
  ((alloc_ceiling <= a /\ ~ (sp - STK <= a < sp + XO)) \/
   (sp <= a < sp + XO /\ ~ inFP OUT a) \/
   (exists p n, In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n /\
      ~ inFP FP a) \/
   (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
      fp_spares FP a) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) /\
      ~ inFP FP a)) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp FP ly S W mem md own ly' S' W' mem' md' k a HGx HJX Ha HnG Hc.
  pose proof HJX as (HS0 & HX0 & (memS & HJi & Hag) & Hout).
  assert (HmS : aview segs (w_H W) memS a = aview segs (w_H W) mem a).
  { apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG. }
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
  destruct Hc as [(H1 & H2) | [(H1 & H2) | [(p & n & H1 & H2 & H3 & H4) | [(H1 & H2 & H3 & H4) | (cid & pos & H1 & H2 & H3)]]]].
  - rewrite (F1 a ltac:(lia) ltac:(lia)). exact HmS.
  - exact (Hout a H1 H2).
  - replace a with (p + (a - p)) in * by lia.
    rewrite (F2 p n (a - p) H1 H2 ltac:(lia) H4). exact HmS.
  - rewrite (F3 a H1 H2 H3 H4). exact HmS.
  - rewrite (F4 cid pos a H1 H2 H3). exact HmS.
Qed.
(* the live blocks are pairwise distinct, and two of them share no byte *)
Lemma dj_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. apply req_size_pos. lia. }
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma dj_apart : forall ly S (W : world segs) mem md p n q r a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (q, r) (ablocks B ly S) -> (p, n) <> (q, r) ->
  p <= a < p + req_size n -> ~ (q <= a < q + req_size r).
Proof.
  intros ly S W mem md p n q r a HAR H1 H2 Hne Ha Hb.
  pose proof (sep_blocks segs B LAWS ly S W mem md p n q r HAR H1 H2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* one byte of a val_mem, as an aview; every byte of a val_mem is visible *)
Lemma dj_av1 : forall (W : world segs) (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict (w_H W) m) a n v -> (0 < n)%nat ->
  aview segs (w_H W) m a = Some (YO0f.le_byte v n 0).
Proof.
  intros W m a n v Hv Hn. specialize (Hv 0%nat Hn). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
  unfold aview. rewrite Hv. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma dj_av_ne : forall (W : world segs) (m : word -> option byte) a (n : nat) v x,
  val_mem segs (mrestrict (w_H W) m) a n v -> a <= x < a + Z.of_nat n -> aview segs (w_H W) m x <> None.
Proof.
  intros W m a n v x Hv Hx. unfold aview.
  assert (Hk : (Z.to_nat (x - a) < n)%nat) by lia.
  specialize (Hv (Z.to_nat (x - a)) Hk). rewrite Z2Nat.id in Hv by lia.
  replace (a + (x - a)) with x in Hv by lia. rewrite Hv. discriminate.
Qed.
(* a callee-saved register across a call *)
Lemma dj_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac dj_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Ltac dc_in := repeat (first [left; reflexivity | right]).

(* every byte of every range of fp is a byte the predicate glob names, or a byte of one of the blocks bl *)
Definition fp_in (fp : list (Z * Z)) (glob : Z -> Prop) (bl : list (Z * Z)) : Prop :=
  forall r, In r fp -> forall a, fst r <= a < snd r -> glob a \/ exists b, In b bl /\ fst b <= a < fst b + snd b.
Lemma dj_fp_in_mono : forall fp (g1 g2 : Z -> Prop) bl1 bl2,
  fp_in fp g1 bl1 -> (forall a, g1 a -> g2 a) -> (forall b, In b bl1 -> In b bl2) -> fp_in fp g2 bl2.
Proof.
  intros fp g1 g2 bl1 bl2 H Hg Hb r Hr a Ha. destruct (H r Hr a Ha) as [Ga | (b & Hb1 & Hb2)].
  - left. exact (Hg a Ga).
  - right. exists b. split; [exact (Hb b Hb1) | exact Hb2].
Qed.
Lemma dj_fp_in_app : forall f1 f2 g bl, fp_in f1 g bl -> fp_in f2 g bl -> fp_in (f1 ++ f2) g bl.
Proof.
  intros f1 f2 g bl H1 H2 r Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr]; [exact (H1 r Hr) | exact (H2 r Hr)].
Qed.
Lemma dra_fp_in_nil : forall (g : Z -> Prop) bl, fp_in [] g bl.
Proof. intros g bl r Hr. destruct Hr. Qed.
Lemma dra_fp_in_cons : forall lo hi fp (g : Z -> Prop) bl,
  (forall a, lo <= a < hi -> g a \/ exists b, In b bl /\ fst b <= a < fst b + snd b) -> fp_in fp g bl ->
  fp_in ((lo, hi) :: fp) g bl.
Proof. intros lo hi fp g bl H1 H2 r [<- | Hr]; [exact H1 | exact (H2 r Hr)]. Qed.
Lemma dra_fp_in_map : forall (X : Type) (f : X -> Z * Z) (xs : list X) (g : Z -> Prop) bl,
  (forall x, In x xs -> forall a, fst (f x) <= a < snd (f x) -> g a \/ exists b, In b bl /\ fst b <= a < fst b + snd b) ->
  fp_in (map f xs) g bl.
Proof. intros X f xs g bl H r Hr. apply in_map_iff in Hr as (x & <- & Hx). exact (H x Hx). Qed.
Lemma dra_fp_in_concat : forall (X : Type) (f : X -> list (Z * Z)) (xs : list X) (g : Z -> Prop) bl,
  (forall x, In x xs -> fp_in (f x) g bl) -> fp_in (concat (map f xs)) g bl.
Proof.
  intros X f xs g bl H r Hr. apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (x & <- & Hx).
  exact (H x Hx r Hr).
Qed.
Lemma dj_alist_fp : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> fp_in (alist_fp LA l) (fun a => LA <= a < LA + 16) (alist_blks l).
Proof.
  intros ly S W mem LA l lines (_ & _ & _ & _ & H5 & H6 & _).
  unfold alist_fp, alist_blks, gfp.
  apply dra_fp_in_cons; [intros a Ha; left; exact Ha|].
  apply dj_fp_in_app.
  - destruct (Z.eqb_spec (hl_cap l) 0) as [E | E]; [apply dra_fp_in_nil|].
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & Hg)]; [lia|].
    apply dra_fp_in_cons; [|apply dra_fp_in_nil].
    intros a Ha. right. exists (hl_v l, AREC * hl_cap l).
    split; [apply in_or_app; left; left; reflexivity|]. cbn [fst snd].
    rewrite dra_bzs_length, length_app, dra_concat_text_len in Ha. unfold hl_n in Hj. unfold AREC in *. lia.
  - apply dra_fp_in_map. intros r Hr a Ha. cbn [fst snd] in Ha.
    rewrite dra_bzs_length, length_app in Ha. cbn [length] in Ha.
    right. exists (fst r, Z.of_nat (length (snd r)) + 1).
    split; [apply in_or_app; right; apply in_map_iff; exists r; split; [reflexivity | exact Hr]|].
    cbn [fst snd]. lia.
Qed.
Lemma dj_asrc_fp : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> fp_in (asrc_fp HA h) (fun a => HA <= a < HA + ASRC) (asrc_blks h).
Proof.
  intros ly S W mem HA h
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & _ & H19 & _ & _ & H22 & H23 & _).
  unfold asrc_fp, asrc_blks.
  apply dra_fp_in_cons; [intros a Ha; left; exact Ha|].
  unfold gfp at 1. apply dra_fp_in_cons.
  { intros a Ha. right. exists (hs_partial h, APARTIAL). split; [left; reflexivity|]. cbn [fst snd].
    rewrite dra_bzs_length in Ha. lia. }
  apply dj_fp_in_app; [|apply dj_fp_in_app].
  - apply (dj_fp_in_mono _ _ _ _ _ (dj_alist_fp ly S W mem (HA + 16) (hs_pending h) false H10)).
    + intros a Ha. unfold ASRC. lia.
    + intros b Hb. right. apply in_or_app. left. exact Hb.
  - apply (dj_fp_in_mono _ _ _ _ _ (dj_alist_fp ly S W mem (HA + 64) (hs_expected h) true H22)).
    + intros a Ha. unfold ASRC. lia.
    + intros b Hb. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - apply (dj_fp_in_mono _ _ _ _ _ (dj_alist_fp ly S W mem (HA + 80) (hs_held h) true H23)).
    + intros a Ha. unfold ASRC. lia.
    + intros b Hb. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma dj_aentry_fp : forall ly S (W : world segs) mem e,
  aentry_ok B ly S W mem e -> Z.of_nat (length (re_keys e)) <= re_nheld e ->
  fp_in (aentry_fp e) (fun _ => False) (aentry_blks e).
Proof.
  intros ly S W mem e (_ & _ & _ & _ & _ & _ & H7 & _ & _ & H10 & _ & H12 & _ & _ & _) Hk.
  unfold aentry_fp, aentry_blks, gfp.
  apply dj_fp_in_app.
  - destruct (Z.eqb_spec (re_cap e) 0) as [E | E]; [apply dra_fp_in_nil|].
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & Hg)]; [lia|].
    apply dra_fp_in_cons; [|apply dra_fp_in_nil].
    intros a Ha. right. exists (re_buf e, re_cap e).
    split; [apply in_or_app; left; left; reflexivity|]. cbn [fst snd].
    rewrite dra_bzs_length, length_app in Ha. lia.
  - apply dra_fp_in_cons.
    + intros a Ha. rewrite dra_bzs_length, dra_key_ptrs_len in Ha.
      destruct H12 as [(Hz & Hkeys) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      * rewrite Hkeys in Ha. cbn [length] in Ha. lia.
      * right. exists (re_hp e, re_kh e). split.
        -- apply in_or_app. right. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
        -- cbn [fst snd]. lia.
    + apply dra_fp_in_map. intros k Hk' a Ha. cbn [fst snd] in Ha.
      rewrite dra_bzs_length, length_app in Ha. cbn [length] in Ha.
      right. eexists.
      split; [apply in_or_app; right; apply in_or_app; right; apply in_map_iff; exists k; split; [reflexivity | exact Hk']|].
      cbn [fst snd]. lia.
Qed.
Lemma dj_arelay_fp : forall ly S (W : world segs) mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) es ->
  fp_in (arelay_fp fr_RG G es)
    (fun a => rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
              rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4)
    (arelay_blks G es).
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _) Hk.
  unfold arelay_fp, arelay_blks.
  apply dra_fp_in_cons; [intros a Ha; left; left; exact Ha|].
  apply dra_fp_in_cons; [intros a Ha; left; right; left; exact Ha|].
  apply dra_fp_in_cons; [intros a Ha; left; right; right; exact Ha|].
  apply dra_fp_in_cons; [intros a Ha; right; exists (G, ATABLE); split; [left; reflexivity | cbn [fst snd]; lia]|].
  apply dra_fp_in_concat. intros e He. rewrite Forall_forall in H10, Hk.
  apply (dj_fp_in_mono _ _ _ _ _ (dj_aentry_fp ly S W mem e (H10 e He) (Hk e He))).
  - intros a Ha. destruct Ha.
  - intros b Hb. right. apply in_concat. exists (aentry_blks e).
    split; [apply in_map_iff; exists e; split; [reflexivity | exact He] | exact Hb].
Qed.
Lemma dj_aout_fp : forall ly S (W : world segs) mem c O mx no cap out,
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  fp_in (aout_fp B fr_RG cap out) (fun a => exists r, In r (aout_fp B fr_RG 0 0) /\ fst r <= a < snd r)
    (aout_blks cap out).
Proof.
  intros ly S W mem c O mx no cap out _.
  assert (E : aout_fp B fr_RG cap out = aout_fp B fr_RG 0 0 ++ (if cap =? 0 then [] else [(out, out + cap)]))
    by reflexivity.
  rewrite E. apply dj_fp_in_app.
  - intros r Hr a Ha. left. exists r. split; [exact Hr | exact Ha].
  - unfold aout_blks. destruct (Z.eqb_spec cap 0) as [Ec | Ec]; [apply dra_fp_in_nil|].
    apply dra_fp_in_cons; [|apply dra_fp_in_nil].
    intros a Ha. right. exists (out, cap). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.

(* ---------------- dt_: the literals and the G-membership facts the transports share ---------------- *)
Ltac dt_infp := repeat (first [left; reflexivity | right]).
(* (a) a range that lies inside one read-only segment of the pinned image *)
Definition dt_romb (lo hi : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) &&
    ((Z.of_N (seg_base sg) <=? lo) && (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))) segs.
Lemma dt_rom_of : forall lo hi a, dt_romb lo hi = true -> lo <= a < hi -> in_rom segs a.
Proof.
  intros lo hi a H Ha. unfold dt_romb in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [H0 Hb]. apply andb_prop in Hb as [H1 H2].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hs | split; [exact H0 | lia]].
Qed.
(* the jump table's 36 bytes are read-only image bytes (the same object on B, 0x20e54, with B's words) *)
Lemma dj_jt_rom : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Proof. intros a Ha. exact (dt_rom_of fr_jtab (fr_jtab + 36) a ltac:(vm_compute; reflexivity) Ha). Qed.

(* (b) image B's globals, as literals, for the apartness side conditions *)
Lemma dt_rgv : rg_s fr_RG = 0x5d8e60 /\ rg_src fr_RG = 0x5d8d40 /\ rg_nsrc fr_RG = 0x5d8d20 /\
  rg_capsrc fr_RG = 0x5d8d80 /\ rg_out fr_RG = 0x5d90c0 /\ rg_nout fr_RG = 0x5d8e40 /\
  rg_capout fr_RG = 0x5d90a0 /\ rg_send_max fr_RG = 0x5d8dc0 /\ rg_send_eintr fr_RG = 0x5d8e20 /\
  rg_send_dead fr_RG = 0x5d8e00 /\ rg_gone fr_RG = 0x5d8de0 /\ rg_client fr_RG = 0xa2560 /\
  rg_client_broken fr_RG = 0x5d8d60 /\ rg_lock fr_RG = 0x5d9040 /\ rg_wake fr_RG = 0xa2520.
Proof. repeat split; reflexivity. Qed.
Lemma dt_cst : ASRC = 96 /\ AG_NFD = 0x5d8da0 /\ AG_THREAD_UP = 0x5d8ce0 /\ AG_LISTEN = 0xa2540.
Proof. repeat split; reflexivity. Qed.
(* every arithmetic side condition of this block: the literals, errno's place, and lia *)
Ltac dt_num :=
  let V := fresh "V" in pose proof dt_rgv as V; destruct V as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?);
  let C := fresh "C" in pose proof dt_cst as C; destruct C as (?&?&?&?);
  pose proof HERR_HI; lia.

(* (c) each global cell the model reads is one of the entry's G_fr *)
Definition DR_GK : list (Z * Z) :=
  [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4); (rg_send_max fr_RG, 8); (rg_client fr_RG, 4);
   (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1); (rg_wake fr_RG, 8); (AG_NFD, 4); (AG_THREAD_UP, 1);
   (AG_LISTEN, 4)].
Lemma dt_G_s : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Proof. exact HGs. Qed.
Lemma dt_G_lock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
Proof. exact HGlock. Qed.
Lemma dt_G_src : forall a, rg_src fr_RG <= a < rg_src fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_src fr_RG, 8).
  split; [dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_nsrc : forall a, rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_nsrc fr_RG, 4).
  split; [dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_capsrc : forall a, rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_capsrc fr_RG, 4).
  split; [dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_smax : forall a, rg_send_max fr_RG <= a < rg_send_max fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_send_max fr_RG, 8).
  split; [dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_client : forall a, rg_client fr_RG <= a < rg_client fr_RG + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_client fr_RG, 4).
  split; [dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_sdead : forall a, rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_send_dead fr_RG, 1).
  split; [dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_gone : forall a, rg_gone fr_RG <= a < rg_gone fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_gone fr_RG, 1).
  split; [dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_wake : forall a, rg_wake fr_RG <= a < rg_wake fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_wake fr_RG, 8).
  split; [dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_nfd : forall a, AG_NFD <= a < AG_NFD + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (AG_NFD, 4).
  split; [dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_up : forall a, AG_THREAD_UP <= a < AG_THREAD_UP + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (AG_THREAD_UP, 1).
  split; [dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_listen : forall a, AG_LISTEN <= a < AG_LISTEN + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (AG_LISTEN, 4).
  split; [dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_cbr : forall a, rg_client_broken fr_RG <= a < rg_client_broken fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_client_broken fr_RG, 1).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_sei : forall a, rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_send_eintr fr_RG, 1).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_nout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_nout fr_RG, 8).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_capout : forall a, rg_capout fr_RG <= a < rg_capout fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_capout fr_RG, 8).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_out : forall a, rg_out fr_RG <= a < rg_out fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_out fr_RG, 8).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_err : forall a, as_errno B <= a < as_errno B + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (as_errno B, 4).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Ltac dt_ing := solve
  [ apply dt_G_s; dt_num | apply dt_G_src; lia | apply dt_G_nsrc; lia | apply dt_G_capsrc; lia
  | apply dt_G_smax; lia | apply dt_G_client; lia | apply dt_G_sdead; lia | apply dt_G_gone; lia
  | apply dt_G_wake; lia | apply dt_G_nfd; lia | apply dt_G_up; lia | apply dt_G_listen; lia
  | apply dt_G_cbr; lia | apply dt_G_sei; lia | apply dt_G_nout; lia | apply dt_G_capout; lia
  | apply dt_G_out; lia | apply dt_G_err; lia | apply dt_G_lock; lia ].

(* (d) a byte whose view is kept, and which is a G_fr byte or lies off the image, is kept *)
Lemma dt_G_rng : forall a, inG G_fr a -> 0x10000 <= a < 0x5fc000.
Proof. intros a Hg. exact (pa_img_range a (proj1 (HG a Hg))). Qed.
Lemma dt_rom_rng : forall a, in_rom segs a -> 0x10000 <= a < 0x5fc000.
Proof. intros a (sg & Hs & _ & Hr). apply pa_img_range. exists sg. split; [exact Hs | exact Hr]. Qed.
Lemma dt_bkG : forall (W W' : world segs) mem mem' a, inG G_fr a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Hg Ha. pose proof (dt_G_rng a Hg).
  apply dj_bk; [lia | intros _; exact Hg | exact Ha].
Qed.
Lemma dt_bkN : forall (W W' : world segs) mem mem' a, 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Hr Hi Ha. apply dj_bk; [exact Hr | intros H; exfalso; exact (Hi H) | exact Ha].
Qed.
Lemma dt_reqr : forall p n a, p <= a < p + n -> p <= a < p + req_size n.
Proof. intros p n a H. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma dt_reqi : forall p n a, p <= a < p + n -> 0 <= a - p < req_size n.
Proof. intros p n a H. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma dt_akept1 : forall (W W' : world segs) mem mem' lo hi,
  (forall x, lo <= x < hi -> abyte_kept W mem W' mem' x) -> akept W mem W' mem' [(lo, hi)].
Proof. intros W W' mem mem' lo hi H r Hr a Ha. destruct Hr as [<- | []]. exact (H a Ha). Qed.
Lemma dt_shadow : forall x, SB + x / 8 = shadow_addr x.
Proof. intros x. reflexivity. Qed.
(* the jump table is ROM: two ROM views read it alike *)
Lemma dt_jt_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> rom_view segs W' mem' -> jt_rom W mem -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HR HR' HJ i Hi k Hk. specialize (HJ i Hi k Hk).
  rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem'); [exact HJ|].
  assert (Hrom : in_rom segs (fr_jtab + 4 * i + Z.of_nat k)) by (apply dj_jt_rom; lia).
  rewrite (HR' _ Hrom), (HR _ Hrom). reflexivity.
Qed.

(* (e) the two keepers the model's transport runs on *)
Definition dt_KG (W : world segs) (mem : word -> option byte) (W' : world segs)
  (mem' : word -> option byte) : Prop :=
  forall a, inG G_fr a -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
    ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W mem W' mem' a.
Definition dt_KB (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
  (W' : world segs) (mem' : word -> option byte) : Prop :=
  forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + n -> abyte_kept W mem W' mem' a.

(* (f) the blocks each component of the model names are live *)
Lemma dt_alist_blks : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem LA l lines (_ & _ & _ & _ & _ & H6 & _ & _ & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct H6 as [(Hc & _) | (Hcp & Hin & _)].
    + rewrite (proj2 (Z.eqb_eq (hl_cap l) 0) Hc) in Hb. destruct Hb.
    + assert (Ec : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite Ec in Hb. destruct Hb as [<- | []]. exact Hin.
  - apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in H9. exact (proj1 (H9 r Hr)).
Qed.
Lemma dt_asrc_blks : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem HA h
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & H18 & _ & _ & _ & H22 & H23 & _) b Hb.
  destruct Hb as [<- | Hb]; [exact H18|].
  apply in_app_or in Hb as [Hb | Hb];
    [exact (dt_alist_blks ly S W mem (HA + 16) (hs_pending h) false H10 b Hb)|].
  apply in_app_or in Hb as [Hb | Hb];
    [exact (dt_alist_blks ly S W mem (HA + 64) (hs_expected h) true H22 b Hb)
    | exact (dt_alist_blks ly S W mem (HA + 80) (hs_held h) true H23 b Hb)].
Qed.
Lemma dt_aentry_blks : forall ly S (W : world segs) mem e,
  aentry_ok B ly S W mem e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem e (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & H12 & _ & _ & H15) b Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct H10 as [(Hc & _) | (Hcp & Hin & _)].
    + rewrite (proj2 (Z.eqb_eq (re_cap e) 0) Hc) in Hb. destruct Hb.
    + assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite Ec in Hb. destruct Hb as [<- | []]. exact Hin.
  - apply in_app_or in Hb as [Hb | Hb].
    + destruct H12 as [(Hz & _) | (Hz & Hin & _)].
      * rewrite (proj2 (Z.eqb_eq (re_hp e) 0) Hz) in Hb. destruct Hb.
      * assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
        rewrite Ez in Hb. destruct Hb as [<- | []]. exact Hin.
    + apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.
Lemma dt_arelay_blks : forall ly S (W : world segs) mem G es,
  arelay_at B fr_RG ly S W mem G es -> forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & H8 & _ & H10 & _) b Hb.
  destruct Hb as [<- | Hb]; [exact H8|].
  apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
  rewrite Forall_forall in H10. exact (dt_aentry_blks ly S W mem e (H10 e He) b Hb).
Qed.
Lemma dt_aout_blks : forall ly S (W : world segs) mem c O mx no cap out,
  aout_at B fr_RG ly S W mem c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem c O mx no cap out
    (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& H26) b Hb.
  unfold aout_blks in Hb. destruct H26 as [(Hc & _) | (Hcp & _ & Hin & _)].
  - rewrite (proj2 (Z.eqb_eq cap 0) Hc) in Hb. destruct Hb.
  - assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Ec in Hb. destruct Hb as [<- | []]. exact Hin.
Qed.

(* (g) the model with g_lock's state a parameter and errno's value free *)
Definition amodel_ne (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (m : lmod)
  (held : bool) : Prop :=
  length (lm_hs m) = 4%nat /\ (forall i, (i < 4)%nat -> aslot B ly S W mem i (nth i (lm_hs m) None)) /\
  arelay_at B fr_RG ly S W mem (lm_G m) (lm_es m) /\
  (exists ev, aout_at B fr_RG ly S W mem (dc_ctl (lm_c m) ev) (lm_O m) (lm_mx m) (Z.of_nat (length (lm_O m)))
                (lm_cap m) (lm_out m)) /\
  agone_at fr_RG W mem (lm_gn m) /\ alock_at fr_RG W mem held /\ awake_at fr_RG W mem /\
  val_mem segs (arm W mem) AG_NFD 4 (lm_nfd m) /\ awr W mem AG_NFD 4 /\ 0 <= lm_nfd m <= OPS_MAX /\
  val_mem segs (arm W mem) AG_THREAD_UP 1 0 /\
  (exists lst, val_mem segs (arm W mem) AG_LISTEN 4 lst) /\ awr W mem AG_LISTEN 4.
Lemma dj_ne_of_at : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m -> amodel_ne ly S W mem m false.
Proof.
  intros ly S W mem m (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split; [exists (ct_ev (lm_c m)); rewrite dc_ctl_eta; exact M4|].
  repeat (split; [assumption|]). exact M13.
Qed.
(* the output stream, with errno re-read at the new state *)
Lemma dt_aoutg : forall a, (exists r, In r (aout_fp B fr_RG 0 0) /\ fst r <= a < snd r) ->
  inG G_fr a /\ ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8).
Proof.
  intros a (r & Hin & Ha). unfold aout_fp in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd] in Ha;
    (split; [dt_ing | dt_num]).
Qed.
Lemma dt_aout_ne : forall ly S (W : world segs) mem (W' : world segs) mem' c O mx no cap out ev,
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  dt_KG W mem W' mem' -> dt_KB ly S W mem W' mem' ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  aout_at B fr_RG ly S W' mem' (dc_ctl c ev) O mx no cap out.
Proof.
  intros ly S W mem W' mem' c O mx no cap out ev HO KG KB HEV HEW HEB.
  assert (AK : forall lo hi, In (lo, hi) (aout_fp B fr_RG cap out) ->
                 (forall x, lo <= x < hi -> ~ (as_errno B <= x < as_errno B + 4)) ->
                 forall x, lo <= x < hi -> abyte_kept W mem W' mem' x).
  { intros lo hi Hin Hne x Hx.
    destruct (dj_aout_fp ly S W mem c O mx no cap out HO (lo, hi) Hin x Hx) as [Hg | ([p n] & Hb & Hab)].
    - destruct (dt_aoutg x Hg) as (P1 & P2). exact (KG x P1 P2 (Hne x Hx)).
    - cbn [fst snd] in Hab.
      exact (KB p n x (dt_aout_blks ly S W mem c O mx no cap out HO (p, n) Hb) Hab). }
  pose proof HO as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 &
                    _ & _ & _ & H20 & H21 & H22 & H23 & H24 & H25 & H26).
  unfold dc_ctl. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_send_max fr_RG) (rg_send_max fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H1]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_send_max fr_RG) (rg_send_max fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_nout fr_RG) (rg_nout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H3]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_nout fr_RG) (rg_nout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H4]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_capout fr_RG) (rg_capout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H5]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_capout fr_RG) (rg_capout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_out fr_RG) (rg_out fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H7]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_out fr_RG) (rg_out fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_client fr_RG) (rg_client fr_RG + 4));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H9]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_client fr_RG) (rg_client fr_RG + 4));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx;
    apply (AK (rg_client_broken fr_RG) (rg_client_broken fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H11]|].
  split; [apply (akept_awr W mem); [intros x Hx;
    apply (AK (rg_client_broken fr_RG) (rg_client_broken fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_send_dead fr_RG) (rg_send_dead fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H13]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_send_dead fr_RG) (rg_send_dead fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_send_eintr fr_RG) (rg_send_eintr fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_send_eintr fr_RG) (rg_send_eintr fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H16]|].
  split; [exact HEV|]. split; [exact HEW|]. split; [exact HEB|].
  split; [exact H20|]. split; [exact H21|]. split; [exact H22|]. split; [exact H23|].
  split; [exact H24|]. split; [exact H25|].
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
  exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  exact (KB out cap x (dt_aout_blks ly S W mem c O mx no cap out HO (out, cap)
           ltac:(unfold aout_blks; rewrite Ec; left; reflexivity)) ltac:(lia)).
Qed.
(* (h) the model, under the two keepers, with the lock and errno given at the new state *)
Lemma dt_ne_core : forall ly S (W : world segs) mem (W' : world segs) mem' m (held held' : bool) ev,
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m) ->
  amodel_ne ly S W mem m held ->
  dt_KG W mem W' mem' -> dt_KB ly S W mem W' mem' ->
  alock_at fr_RG W' mem' held' ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  amodel_ne ly S W' mem' m held'.
Proof.
  intros ly S W mem W' mem' m held held' ev HK
    (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13) KG KB HLK HEV HEW HEB.
  split; [exact M1|].
  split.
  { intros i Hi. pose proof (M2 i Hi) as Mi. assert (Hi4 : Z.of_nat i < 4) by lia.
    unfold aslot in Mi |- *. destruct (nth i (lm_hs m) None) as [h|].
    - apply (asrc_at_kept B ly S W mem ly S W' mem' (rg_s fr_RG + ASRC * Z.of_nat i) h Mi).
      + intros r Hr a Ha.
        destruct (dj_asrc_fp ly S W mem (rg_s fr_RG + ASRC * Z.of_nat i) h Mi r Hr a Ha)
          as [Hg | ([p n] & Hb & Hab)].
        * apply KG; [apply dt_G_s; dt_num | dt_num | dt_num].
        * cbn [fst snd] in Hab.
          exact (KB p n a (dt_asrc_blks ly S W mem _ h Mi (p, n) Hb) Hab).
      + intros b Hb. exact (dt_asrc_blks ly S W mem _ h Mi b Hb).
    - destruct Mi as (G1 & G2).
      assert (HL : length (repeat 0 (Z.to_nat ASRC)) = 96%nat) by (vm_compute; reflexivity).
      split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite HL in Hx.
        apply KG; [apply dt_G_s; dt_num | dt_num | dt_num].
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply KG; [apply dt_G_s; dt_num | dt_num | dt_num]. }
  split.
  { apply (arelay_at_kept B fr_RG ly S W mem ly S W' mem' (lm_G m) (lm_es m) M3).
    - intros r Hr a Ha.
      destruct (dj_arelay_fp ly S W mem (lm_G m) (lm_es m) M3 HK r Hr a Ha) as [Hg | ([p n] & Hb & Hab)].
      + destruct Hg as [Hg | [Hg | Hg]]; apply KG; solve [dt_ing | dt_num].
      + cbn [fst snd] in Hab.
        exact (KB p n a (dt_arelay_blks ly S W mem (lm_G m) (lm_es m) M3 (p, n) Hb) Hab).
    - intros b Hb. exact (dt_arelay_blks ly S W mem (lm_G m) (lm_es m) M3 b Hb). }
  split.
  { destruct M4 as (ev0 & HO). exists ev.
    exact (dt_aout_ne ly S W mem W' mem' (dc_ctl (lm_c m) ev0) (lm_O m) (lm_mx m)
             (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) ev HO KG KB HEV HEW HEB). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' (lm_gn m) M5).
    apply dt_akept1. intros x Hx. apply KG; [apply dt_G_gone; lia | dt_num | dt_num]. }
  split; [exact HLK|].
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    apply dt_akept1. intros x Hx. apply KG; [apply dt_G_wake; lia | dt_num | dt_num]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx.
    apply KG; [apply dt_G_nfd; dt_num | dt_num | dt_num]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx.
    apply KG; [apply dt_G_nfd; lia | dt_num | dt_num]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx.
    apply KG; [apply dt_G_up; dt_num | dt_num | dt_num]. }
  split.
  { destruct M12 as (lst & Hlst). exists lst. apply (akept_vm W mem); [|exact Hlst]. intros x Hx.
    apply KG; [apply dt_G_listen; dt_num | dt_num | dt_num]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx.
  apply KG; [apply dt_G_listen; lia | dt_num | dt_num].
Qed.
(* a pthread_mutex_lock / _unlock step (aj_gx_entry_at's post): every byte but the lock word and the entry's
   scratch [sp - ESTACK, sp) keeps its view *)
Lemma dj_ne_lockstep : forall ly S (W : world segs) mem md mem' m (held held' : bool) sp,
  AR segs B ly S W mem md ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m) ->
  amodel_ne ly S W mem m held ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) -> ~ (sp - ESTACK <= a < sp) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  alloc_ceiling + 8 <= sp - ESTACK ->
  val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 (if held' then 16 else 0) ->
  amodel_ne ly S W mem' m held'.
Proof.
  intros ly S W mem md mem' m held held' sp HAR HK HM KV Hsp HLW.
  pose proof asan_consts as ((HCL & HCU) & _).
  assert (KGall : forall a, inG G_fr a -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
                    abyte_kept W mem W mem' a).
  { intros a Hg Hl. pose proof (dt_G_rng a Hg) as Hr.
    apply dt_bkG; [exact Hg|]. apply KV; [lia | exact Hl | lia]. }
  assert (KG : dt_KG W mem W mem') by (intros a Hg Hl _; exact (KGall a Hg Hl)).
  assert (KB : dt_KB ly S W mem W mem').
  { intros p n a Hin Ha.
    destruct (dr_blk ly S W mem md p n HAR Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img segs B LAWS ly S W mem md p n a HAR Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; apply Hni; exact (proj1 (HG a (dt_G_lock a ltac:(lia)))) | lia]. }
  pose proof HM as (_ & _ & _ & (ev0 & HO) & _ & M6 & _).
  assert (HLK : alock_at fr_RG W mem' held').
  { destruct M6 as (L1 & L2 & L3 & L4).
    split; [apply (akept_vm W mem); [|exact L1]; intros x Hx;
      apply KGall; [apply dt_G_lock; dt_num | dt_num]|].
    split; [exact HLW|].
    split; [apply (akept_vm W mem); [|exact L3]; intros x Hx;
      apply KGall; [apply dt_G_lock; dt_num | dt_num]|].
    intros i Hi. exact (GWR _ _ (rg_lock fr_RG + i) (dt_G_lock (rg_lock fr_RG + i) ltac:(lia))). }
  pose proof HO as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& E1 & E2 & E3 & _).
  assert (KE : forall x, as_errno B <= x < as_errno B + 4 -> abyte_kept W mem W mem' x)
    by (intros x Hx; apply KGall; [apply dt_G_err; lia | dt_num]).
  exact (dt_ne_core ly S W mem W mem' m held held' (ct_ev (dc_ctl (lm_c m) ev0)) HK HM KG KB HLK
           (akept_vm W mem W mem' (as_errno B) 4 (ct_ev (dc_ctl (lm_c m) ev0))
              ltac:(intros x Hx; apply KE; dt_num) E1)
           (akept_awr W mem W mem' (as_errno B) 4 ltac:(intros x Hx; apply KE; lia) E2) E3).
Qed.

(* ---------------- the journal's own facts: the frame base, the live frame, the layout ---------------- *)
Lemma dcF_F : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320 /\ lf_F cx mod 32 = 0 /\
  (lf_F cx - spZ (c_regs cx)) mod 16 = 0 /\ alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
  Z.of_nat (length (c_pl cx)) = c_n cx.
Proof.
  intros cx HB.
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  assert (Ho16 : (F - sp0) mod 16 = 0).
  { assert (HF32' : F = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
    pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
    rewrite HF32'.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  repeat split; first [exact Ho16 | exact Hnlen | exact HF32 | lia].
Qed.
Lemma dcF_fin : forall cx fpos ly S (W : world segs) mem md k,
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k ->
  In (1, fpos) (frames S).
Proof.
  intros cx fpos ly S W mem md k HJ.
  pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
  rewrite Hfrs. left. reflexivity.
Qed.
(* a callee never moves the frame area: ly_F, hence the fake frame's base and its flag word, are the same *)
Lemma dcF_lyF : forall G XO OUT STK sp FP ly S (W : world segs) mem md own ly' S' (W' : world segs) mem' md' k,
  ajournal_gx segs B G XO OUT STK sp FP ly S W mem md own ly' S' W' mem' md' k -> ly_F ly' = ly_F ly.
Proof.
  intros G XO OUT STK sp FP ly S W mem md own ly' S' W' mem' md' k HJ.
  pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _). exact EF.
Qed.
Lemma dcF_frame_eq : forall G XO OUT STK sp FP ly S (W : world segs) mem md own ly' S' (W' : world segs) mem' md' k
  (cid pos : Z),
  ajournal_gx segs B G XO OUT STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
  intros G XO OUT STK sp FP ly S W mem md own ly' S' W' mem' md' k cid pos HJ.
  pose proof (dcF_lyF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as EF.
  unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.
(* the whole function window is present at the end of any journal from the entry, hence writable *)
Lemma dcF_pres : forall cx fpos ly S (W : world segs) mem md k,
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k ->
  forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem a.
Proof.
  intros cx fpos ly S W mem md k HJ.
  pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  intros a Ha. exact (Hpres a Ha).
Qed.

(* ---------------- the frame, the input and the context across a callee ---------------- *)
(* the frame cells, the fake frame and its shadow.  The `at` cell F + DR_AT is the one byte range the window
   [F, sp0) may lose: check_no_loss writes it through its out-parameter window.  No frame cell meets it
   (the prologue's highest is F + 184, and 184 + 8 = 192 = DR_AT). *)
Lemma dc_aframe_kept : forall cx FF (W W' : world segs) mem mem',
  aframe_at cx FF W mem -> lf_F cx + 320 <= spZ (c_regs cx) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
     abyte_kept W mem W' mem' a) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W' mem') a) ->
  (forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a) ->
  (forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a) ->
  aframe_at cx FF W' mem'.
Proof.
  intros cx FF W W' mem mem'
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20
     & A21 & A22) HF KS WF KFF KSH.
  unfold DR_AT in *.
  assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) ->
      (a + 8 <= lf_F cx + 192 \/ lf_F cx + 200 <= a) -> sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 H2 Hv. apply (dr_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply KS; lia. }
  assert (KVF : forall a v, FF <= a -> a + 8 <= FF + 128 -> sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 Hv. apply (dr_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply KFF; lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | lia | exact (A1 o r Hin)]. }
  split; [intros i Hi; apply WF; lia|].
  do 14 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split; [apply KVF; [lia | lia | exact A17]|].
  split; [apply KVF; [lia | lia | exact A18]|].
  split; [apply KVF; [lia | lia | exact A19]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KFF; lia | exact A20]|].
  split.
  - apply (akept_garr8 W mem); [|exact A21].
    intros x Hx. unfold fake_shadow in Hx. cbn [length] in Hx. apply KSH; lia.
  - apply (akept_awr W mem); [intros x Hx; apply KSH; lia | exact A22].
Qed.
(* the writability of [F, sp0) at the new state, from a keeper with no hole *)
Lemma dc_wf_of_kept : forall cx FF (W W' : world segs) mem mem',
  aframe_at cx FF W mem ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W' mem' a) ->
  forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W' mem') a.
Proof.
  intros cx FF W W' mem mem' (_ & A2 & _) KS a Ha.
  destruct (KS a Ha) as (_ & Hw). apply Hw.
  replace a with (lf_F cx + (a - lf_F cx)) by lia. apply A2. lia.
Qed.
Lemma dt_ainput_kept : forall cx ly S (W : world segs) mem (W' : world segs) mem',
  ainput_at B cx ly S W mem -> Z.of_nat (length (c_pl cx)) = c_n cx ->
  dt_KB ly S W mem W' mem' -> ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem W' mem' (H1 & H2) Hlen KB.
  split; [exact H1|]. apply (akept_garr8 W mem); [|exact H2].
  intros x Hx. rewrite length_map, Hlen in Hx.
  destruct H1 as [(Hn0 & _) | (Hn & Hin)]; [lia|]. exact (KB (c_p cx) (c_n cx) x Hin Hx).
Qed.
(* the facts of a state that are not the model: the frame, the fake frame's flag word, the input, the ROM, the
   jump table and the in.n cell.  The `at` cell is carried beside this record, because check_no_loss changes it. *)
Definition dc_ctxp (cx : lfcx) (m : lmod) (FF flag : Z) (ly : alayout) (S : astate) (W : world segs)
  (mem : word -> option byte) : Prop :=
  aframe_at cx FF W mem /\ sv8 W mem (FF + 120) flag /\ ainput_at B cx ly S W mem /\
  rom_view segs W mem /\ jt_rom W mem /\ sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m).
Lemma dc_ctx_core : forall cx m FF flag ly S (W : world segs) mem (W' : world segs) mem',
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  dc_ctxp cx m FF flag ly S W mem ->
  (forall a, lf_F cx <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
     abyte_kept W mem W' mem' a) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W' mem') a) ->
  (forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a) ->
  (forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a) ->
  dt_KB ly S W mem W' mem' -> rom_view segs W' mem' ->
  dc_ctxp cx m FF flag ly S W' mem'.
Proof.
  intros cx m FF flag ly S W mem W' mem' HLB (HFR & HFL & HIN & HRV & HJT & HN) KS WF KFF KSH KB HRV'.
  destruct (dcF_F cx HLB) as (Q1 & Q2 & Q3 & Q4 & Q5).
  assert (KS' : forall a, lf_F cx <= a < spZ (c_regs cx) ->
      ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) -> abyte_kept W mem W' mem' a)
    by (intros a Ha Hn; apply KS; [lia | exact Hn]).
  split; [exact (dc_aframe_kept cx FF W W' mem mem' HFR ltac:(lia) KS' WF KFF KSH)|].
  split; [apply (dr_sv8_kept W W' mem mem'); [intros x Hx; apply KFF; lia | exact HFL]|].
  split; [exact (dt_ainput_kept cx ly S W mem W' mem' HIN Q5 KB)|].
  split; [exact HRV'|].
  split; [exact (dt_jt_kept W W' mem mem' HRV HRV' HJT)|].
  apply (dr_sv8_kept W W' mem mem'); [|exact HN].
  intros x Hx. apply KS; unfold DR_N, DR_AT in *; lia.
Qed.
(* the context across a lock / unlock entry *)
Lemma dj_ctx_lockstep : forall cx m FF flag ly S (W : world segs) mem md mem',
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  AR segs B ly S W mem md -> (exists pos, In (1, pos) (frames S) /\ FF = frame_addr ly 1 pos) ->
  dc_ctxp cx m FF flag ly S W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
     ~ (lf_F cx - ESTACK <= a < lf_F cx) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  dc_ctxp cx m FF flag ly S W mem' /\
  (forall v, sv8 W mem (lf_F cx + DR_AT) v -> sv8 W mem' (lf_F cx + DR_AT) v).
Proof.
  intros cx m FF flag ly S W mem md mem' HLB HAR (pos & Hfin & HFF) HCX KV HPR.
  pose proof asan_consts as ((HCL & HCU) & HSE & _ & HME & HLE).
  assert (HES : ESTACK = 4096) by reflexivity.
  destruct (dcF_F cx HLB) as (Q1 & Q2 & Q3 & Q4 & Q5).
  destruct (frames_bounds segs B LAWS ly S W mem md 1 pos HAR Hfin) as (HF1 & HF2 & _).
  change (fs_frame_bytes 1) with 128 in HF2. rewrite <- HFF in HF1, HF2.
  pose proof (dt_shadow FF) as Hsh.
  pose proof (shadow_addr_bounds FF ltac:(lia)) as Hsb.
  pose proof (shadow_addr_bounds (FF + 128) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end FF 128 ltac:(lia)) as Hsr.
  assert (Hlockimg : forall a, rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8 -> in_img segs a)
    by (intros a Ha; exact (proj1 (HG a (dt_G_lock a ltac:(lia))))).
  assert (KS : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  assert (KFF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a)
      by (apply (frm_img segs B LAWS ly S W mem md 1 pos a HAR Hfin);
          rewrite <- HFF; change (fs_frame_bytes 1) with 128; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  assert (KSH : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  assert (KB : dt_KB ly S W mem W mem').
  { intros p n a Hin Ha.
    destruct (dr_blk ly S W mem md p n HAR Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img segs B LAWS ly S W mem md p n a HAR Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  assert (HRV' : rom_view segs W mem').
  { pose proof HCX as (_ & _ & _ & HRV & _). intros a Ha. pose proof (dt_rom_rng a Ha) as Hr.
    rewrite (KV a ltac:(lia) ltac:(intros Hc; exact (proj1 (DR_ROM_OUT a Ha) (dt_G_lock a ltac:(lia))))
               ltac:(lia)).
    exact (HRV a Ha). }
  assert (WF : forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W mem') a)
    by exact (dc_wf_of_kept cx FF W W mem mem' (proj1 HCX) ltac:(intros a Ha; apply KS; lia)).
  split;
    [exact (dc_ctx_core cx m FF flag ly S W mem W mem' HLB HCX ltac:(intros a Ha _; apply KS; lia) WF KFF KSH KB HRV')|].
  intros v Hv. apply (dr_sv8_kept W W mem mem'); [|exact Hv]. intros x Hx. apply KS. unfold DR_AT in *. lia.
Qed.
(* a leaf callee (no footprint, the allocator state kept) called at sp = F *)
Lemma dj_ne_plain : forall ly S (W W' : world segs) mem mem' md md' m held STK sp,
  ajournal segs B STK sp [] ly S W mem md [] ly S W' mem' md' 0 -> alloc_ceiling + 8 <= sp - STK ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m) ->
  amodel_ne ly S W mem m held -> amodel_ne ly S W' mem' m held.
Proof.
  intros ly S W W' mem mem' md md' m held STK sp HJ Hsp HK HM.
  pose proof asan_consts as ((HCL & HCU) & _).
  pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & F3 & _).
  assert (KGall : forall a, inG G_fr a -> ~ (as_errno B <= a < as_errno B + 4) ->
                    abyte_kept W mem W' mem' a).
  { intros a Hg He. destruct (HG a Hg) as (Hi & Ho & _).
    apply dt_bkG; [exact Hg|].
    apply F3; [exact Hi | exact Ho | exact He |].
    apply fp_spares_closed. intros (r & Hr & _). destruct Hr. }
  assert (KG : dt_KG W mem W' mem') by (intros a Hg _ He; exact (KGall a Hg He)).
  assert (KB : dt_KB ly S W mem W' mem').
  { intros p n a Hin Ha.
    destruct (dr_blk ly S W' mem' md' p n HAR' Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img segs B LAWS ly S W' mem' md' p n a HAR' Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    replace a with (p + (a - p)) by lia.
    apply (F2 p n (a - p) Hin Hin (dt_reqi p n a Ha)). intros Hc. exact (inFP_nil _ Hc). }
  pose proof HM as (_ & _ & _ & _ & _ & M6 & _).
  assert (HLK : alock_at fr_RG W' mem' held).
  { apply (alock_at_kept fr_RG W mem W' mem' held M6). apply dt_akept1. intros x Hx.
    apply KGall; [apply dt_G_lock; lia | dt_num]. }
  destruct (ERR ly S W' mem' md' HAR') as ((ev & HEV & HEB) & HEW).
  exact (dt_ne_core ly S W mem W' mem' m held held ev HK HM KG KB HLK HEV HEW HEB).
Qed.
Lemma dj_ctx_plain : forall cx m FF flag ly S (W W' : world segs) mem mem' md md' STK,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal segs B STK (lf_F cx) [] ly S W mem md [] ly S W' mem' md' 0 -> 0 <= STK <= 16384 ->
  (exists pos, In (1, pos) (frames S) /\ FF = frame_addr ly 1 pos) ->
  dc_ctxp cx m FF flag ly S W mem ->
  dc_ctxp cx m FF flag ly S W' mem' /\
  (forall v, sv8 W mem (lf_F cx + DR_AT) v -> sv8 W' mem' (lf_F cx + DR_AT) v).
Proof.
  intros cx m FF flag ly S W W' mem mem' md md' STK HLB HJ HSTK (pos & Hfin & HFF) HCX.
  pose proof asan_consts as ((HCL & HCU) & HSE & _ & HME & HLE).
  destruct (dcF_F cx HLB) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _ & Fpres & _).
  destruct (frames_bounds segs B LAWS ly S W' mem' md' 1 pos HAR' Hfin) as (HF1 & HF2 & _).
  change (fs_frame_bytes 1) with 128 in HF2. rewrite <- HFF in HF1, HF2.
  pose proof (dt_shadow FF) as Hsh.
  pose proof (shadow_addr_bounds FF ltac:(lia)) as Hsb.
  pose proof (shadow_addr_bounds (FF + 128) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end FF 128 ltac:(lia)) as Hsr.
  assert (KS : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|]. apply F1; lia. }
  assert (KFF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a)
      by (apply (frm_img segs B LAWS ly S W' mem' md' 1 pos a HAR' Hfin);
          rewrite <- HFF; change (fs_frame_bytes 1) with 128; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply (F4 1 pos a Hfin); [left | intros Hc; exact (inFP_nil _ Hc)].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- HFF.
    change (fs_frame_bytes 1) with 128. lia. }
  assert (KSH : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply (F4 1 pos a Hfin); [right | intros Hc; exact (inFP_nil _ Hc)].
    unfold in_zr. cbn [fst snd]. rewrite <- HFF.
    change (fs_frame_bytes 1) with 128. change (128 / 8) with 16. rewrite <- dt_shadow. lia. }
  assert (KB : dt_KB ly S W mem W' mem').
  { intros p n a Hin Ha.
    destruct (dr_blk ly S W' mem' md' p n HAR' Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img segs B LAWS ly S W' mem' md' p n a HAR' Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    replace a with (p + (a - p)) by lia.
    apply (F2 p n (a - p) Hin Hin (dt_reqi p n a Ha)). intros Hc. exact (inFP_nil _ Hc). }
  assert (HRO : rom_out segs B []).
  { intros a Ha. destruct (DR_ROM_OUT a Ha) as (_ & R2 & R3 & R4).
    split; [intros Hc; exact (inG_nil a Hc)|]. split; [exact R2 | split; [exact R3 | exact R4]]. }
  assert (HJx : ajournal_gx segs B [] 0 [] STK (lf_F cx) [] ly S W mem md [] ly S W' mem' md' 0)
    by (apply ajournal_gx_nil; exact HJ).
  assert (HRV' : rom_view segs W' mem').
  { pose proof HCX as (_ & _ & _ & HRV & _).
    eapply ajournal_gx_rom_view; first [exact HJx | exact HRO | exact HRV | exact LAWS | exact pa_segs_low]. }
  assert (WF : forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W' mem') a)
    by exact (dc_wf_of_kept cx FF W W' mem mem' (proj1 HCX) ltac:(intros a Ha; apply KS; lia)).
  split;
    [exact (dc_ctx_core cx m FF flag ly S W mem W' mem' HLB HCX ltac:(intros a Ha _; apply KS; lia) WF KFF KSH KB HRV')|].
  intros v Hv. apply (dr_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply KS. unfold DR_AT in *. lia.
Qed.

(* ---------------- the registers the six calls keep, and the states between them ---------------- *)
(* dr_regs_call (the interface's) plus s7: &g_lock up to 0x84910, then 1 *)
Definition dc_regs (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (FF s7v : Z) (regs : bvmap 5 word) : Prop :=
  dr_regs_call B cx t m j si FF regs /\ getr regs 23 = w64 s7v.
(* every register dr_regs_call names; s7 (reg 23) is NOT here: 0x84910 writes it *)
Definition dcF_K : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv.
Lemma dcF_pres_K : forall regs regs', aregs_preserved regs regs' ->
  forall r, In r dcF_K -> getr regs' r = getr regs r.
Proof.
  intros regs regs' HP r Hr. apply (dj_pres regs regs' r HP). unfold dcF_K in Hr.
  repeat (destruct Hr as [<- | Hr]; [dj_cs|]). destruct Hr.
Qed.
Lemma dcF_regs_kept : forall cx t m j si FF s7v s7v' regs regs',
  (forall r, In r dcF_K -> getr regs' r = getr regs r) -> getr regs' 23 = w64 s7v' ->
  dc_regs cx t m j si FF s7v regs -> dc_regs cx t m j si FF s7v' regs'.
Proof.
  intros cx t m j si FF s7v s7v' regs regs' HK H23
    ((R2 & R8 & R9 & R18 & R19 & R24 & R26 & R27 & R3 & R4 & R25 & Ht & R20 & R21 & R22) & _).
  split; [|exact H23].
  unfold dr_regs_call. rewrite !HK by (cbv; tauto).
  exact (conj R2 (conj R8 (conj R9 (conj R18 (conj R19 (conj R24 (conj R26 (conj R27 (conj R3 (conj R4
    (conj R25 (conj Ht (conj R20 (conj R21 R22)))))))))))))).
Qed.
(* a part of a zero-shadow range is one *)
Lemma dcF_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof. intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|]. repeat split; lia. Qed.

(* a state of the arm between two of its calls: the journal from the entry, the registers, the context, the `at`
   cell, the model with the lock's state and the entries' key-count bound *)
Definition dc_at (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (fpos FF pc : Z) (ly : alayout) (S : astate)
  (mc : lmod) (held : bool) (A s7v : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md k,
    c = mkCfg (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)) md /\
    dc_regs cx t m j si FF s7v regs /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k /\
    frame_addr ly 1 fpos = FF /\
    dc_ctxp cx m FF (flag_addr ly 1 fpos) ly S W mem /\
    sv8 W mem (lf_F cx + DR_AT) A /\
    amodel_ne ly S W mem mc held /\ ablocks_sep B fr_FP cx mc ly S /\
    Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es mc).
(* what the arm knows of the model before the drain *)
Definition dc_static (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (h : hsrc) : Prop :=
  dr_at_op cx m /\ dr_pick cx m si h /\ (j < length (lm_es m))%nat /\
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\ re_eof (nth j (lm_es m) dr_e0) = 0 /\ RINV cx t m.

(* ---------------- the call machinery: the callee's afn_pre at sp = F, and the journal composition -------- *)
Lemma dr_afn_pre_at : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
  pose proof HFR as (HSV & _).
  assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  clear Hpres0.
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hsp8 : sp0 mod 8 = 0).
  { assert (Hq : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    rewrite Hq. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  assert (HCH : exists ch, achain ly3 (aview segs (w_H W) mem) (lf_F cx) sp0 ch).
  { destruct (Z_lt_ge_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
    - exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
      apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
      eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
        sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
        [ exact Hch0 | lia
        | intros a Ha; rewrite (HAB a ltac:(lia)); apply HSG; rewrite unsigned_lit_small by lia; intros HGa;
          pose proof (inG_low segs B pa_segs_low G_fr a HG HGa); lia
        | exact Hra8 | exact Hs016
        | unfold raZ in Hra40; lia | lia | exact Hsp8 | exact Hlt | rewrite HF32; lia ].
    - exists []. left. split; [right; left; rewrite HTOPeq; lia | reflexivity]. }
  destruct HCH as (ch & HCH).
  exists ch.
  eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
    [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
    | exact Hgp | exact Htp | ].
  rewrite Hsp. replace (s0Z regs) with sp0 by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  exact HCH.
Qed.
(* the caller's stack is readable from the arm's frame base up to ly_top, at any state the arm's journal reaches:
   the kit's cnl_spec asks it at the check_no_loss call (lib/B/W_contract.v:2087, sp = F).  [F, sp0) is the
   function's own window, present at the end of the journal (dcF_pres); [sp0, ly_top) is the cut's STKR at the
   entry (fr_lib_pre_cf's 18th conjunct, before HB), kept to here because the journal changes no byte above its window
   (aview_above_of_journal) and no stack byte is a G_fr byte (inG_low: G_fr lies in the image). *)
Lemma dcF_stk_rd : forall cx ly3 S3 fpos (W : world segs) mem md k,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  forall a, lf_F cx <= a < ly_top ly3 -> aview segs (w_H W) mem a <> None.
Proof.
  intros cx ly3 S3 fpos W mem md k HB HJ a Ha.
  pose proof (dcF_F cx HB) as (HFb & _ & _ & Hsp0 & _).
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2).
  (* STKR, the 18th conjunct of the cut's fr_lib_pre_cf (lib/B/W_LLVMFuzzerTestOneInput_cut.v:293); HB follows it as the
     19th and last (:282), so an explicit destruct, not a repeat that would also open HB *)
  assert (HSTKR : forall x, spZ (c_regs cx) <= x < ly_top (c_ly cx) ->
                    aview segs (w_H (c_W cx)) (c_mem cx) x <> None).
  { unfold fr_lib_pre_cf in HPRE.
    destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKR0 & _).
    exact HSTKR0. }
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  set (sp0 := spZ (c_regs cx)) in *.
  destruct (Z_lt_le_dec a sp0) as [Hlo | Hhi].
  - apply aview_some_of_apresent.
    exact (dcF_pres cx fpos ly3 S3 W mem md k HJ a ltac:(unfold LLVMF_STK; lia)).
  - pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
    rewrite (HAB a ltac:(lia)).
    rewrite (HSG a).
    + apply HSTKR. lia.
    + (* 0 <= a needs the ceiling's own bound: alloc_ceiling is opaque to lia *)
      pose proof dr_ceil_lo as Hcl.
      assert (Ha64 : 0 <= a < 2 ^ 64) by (clear - Ha Hhi HTOPeq Htop2 H47 Hsp0 Hcl; lia).
      rewrite (unsigned_lit_small a Ha64). intros HGa.
      pose proof (inG_low segs B pa_segs_low G_fr a HG HGa) as Hlow.
      unfold kLowMemEnd in Hlow. clear - Hlow Hcl Hhi Hsp0. lia.
Qed.
(* a call to a program function inside this walk, with the callee's journal composed into the caller's *)
Lemma dr_callZ : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1
  XO1 OUT1 (o : Z) raw ch1
  (K : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  gx_ok segs B G ->
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o <= 0 -> STK1 - o <= STK ->
  0 <= XO1 -> o + XO1 <= 0 -> (forall a, inFP OUT1 a -> sp0 - STK <= a < sp0) ->
  getr regsc 1 = raw ->
  afn_pre segs B STK1 lyc Sc W regsc memc mdc ch1 ->
  SRr segs W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
   (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal_gx segs B G XO1 OUT1 STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 /\
    aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2) ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
   in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr segs W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
   c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
   ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + k1) /\
   ajournal_gx segs B G XO1 OUT1 STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 /\
   aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
  intros G W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 XO1 OUT1 o raw ch1 K
    HGx HJ Hsp Hneg Hbud HXO HXO2 HOUT Hra HPRE Hcallee HF.
  eapply SRr_mono; [exact Hcallee|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
  exists ly2, S2, regs2, mem2, md2, k1. split; [reflexivity|].
  rewrite Hsp in HJ1.
  split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
  change own with ([] ++ own).
  pose proof HJ as (HS0 & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & (_ & HS1 & _) & _).
  eapply (ajournal_gx_sub segs B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
  intros a Ha. left. exact (HOUT a Ha).
Qed.

(* ---------------- the symbolic entry states of the four plain run points ---------------- *)
(* B keeps the shadow base SB in s11 (reg 27), image A in reg 26 *)
Definition dr_facts : facts := mkFacts [ (27%nat, mkAF SB SB 0) ] [] [].
Definition drBx : sv := SOff 27 0.
Definition DRspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ss_plain (pc : Z) : sstate := mkSS pc sr_atoms [] None dr_facts.
Lemma dc_plain_entry : forall pc (W : world segs) regs mem,
  getr regs 27 = w64 SB ->
  st_ok_pi segs VAL (Eimg (Ereg regs [])) (ss_plain pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)))
  /\ sh_ok segs drBx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
  intros pc W regs mem R27.
  rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (E27 : ew E 27 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  split.
  - unfold ss_plain. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + constructor.
    + cbn [pairwise_disjoint all_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [dr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E27, unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
(* 0x8492c `ld a0,192(s1)`: one 8-byte frame cell, its value the atom 32 *)
Definition dc_cell (off : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) off (off + 8) 0 0 [YP09.mkChunk off (CVal 8 (SOff 32 0))].
Definition dc_facts9a : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition ss_dc_cell (pc off : Z) : sstate := mkSS pc sr_atoms [dc_cell off] None dc_facts9a.
Definition dc_cell_extra (A : Z) : list word := map (Z_to_bv 64) [A].
Lemma dc_cell_entry : forall pc off (W : world segs) regs mem F A,
  getr regs 9 = w64 F -> getr regs 27 = w64 SB -> 2 ^ 46 <= F -> F + 200 <= 2 ^ 47 -> F mod 32 = 0 ->
  0 <= off -> off + 8 <= 200 -> regions_wf [dc_cell off] = true ->
  sv8 W mem (F + off) A -> 0 <= A < 2 ^ 64 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (dc_cell_extra A))) (ss_dc_cell pc off)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)))
  /\ sh_ok segs drBx [] (Eimg (Ereg regs (dc_cell_extra A))) (mrestrict (w_H W) mem).
Proof.
  intros pc off W regs mem F A R9 R27 HF0 HF1 HF32 Ho0 Ho1 Hwf MA HA.
  rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs (dc_cell_extra A))) as E eqn:HE.
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (E27 : ew E 27 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 A)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - unfold ss_dc_cell. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + exact Hwf.
    + apply Forall_cons; [|constructor]. unfold region_ok, dc_cell.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|constructor].
      apply (chunk_ok_val segs E _ F off 8 (SOff 32 0) A);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MA].
    + cbn [pairwise_disjoint all_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [dc_facts9a f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E27, E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
(* after a run whose regions have no writable window, the memory is the one it began in *)
Ltac dr_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* ================================================================== the six calls, one stage each *)
(* ---- stage A: 0x84900 jal pthread_mutex_lock -> 0x84904.
   Contract: lib/B/W_sites.v:90 alock_realizes at SIGMA WS_pthread_mutex_lock (the interface's dre_ALOCK);
   journal composition: lib/B/W_sites.v:392 aj_gx_entry_at. ---- *)
Lemma dc_stA : forall cx t m j si h fpos ly3 S3 k W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  DLK B G_fr fr_FP LS RINV cx t m j si h fpos ly3 S3 k W c ->
  SRr segs W c (dc_at cx t m j si fpos (frame_addr ly3 1 fpos) A_dr_r1 ly3 S3 m true 0 (rg_lock fr_RG)).
Proof.
  intros cx t m j si h fpos ly3 S3 k W c HB
    (regs & mem & md & -> & HJ & HFR & HFL & HMOD & HIN & HRV & HROM & HSEP & HLS & HRI & Hatop & Hpick & Hj &
     Hfdj & Hef0 & SVN & S192 & Q1 & Q10 & Q23 & HREGS).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : AR segs B ly3 S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof HMOD as (Hlen4 & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  destruct (dcF_F cx HB) as (HFb & HF32 & Ho16 & Hsp0 & Hnlen).
  pose proof HREGS as (R2 & R8 & R9 & R18 & R19 & R24 & R26 & R27 & R3 & R4 & R25 & Ht & R20 & R21 & R22).
  pose proof (dcF_fin cx fpos ly3 S3 W mem md k HJ) as Hfin.
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  assert (VLK : rg_lock fr_RG = 0x5d9040) by reflexivity.
  pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
  assert (HNOWN : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ aowned B ly3 S3 a).
  { intros a Ha Ho. destruct (HG a (HGlock a Ha)) as (Hi & Hno & _).
    apply Hno. exact (proj1 (al_owned_image _ _ LAWS ly3 S3 W mem _ a HAR Hi) Ho). }
  assert (AVL : aview segs (w_H W) mem (rg_lock fr_RG) = Some 0).
  { pose proof (dj_av1 W mem (rg_lock fr_RG) 4%nat 0 LK0 ltac:(lia)) as HA.
    replace (YO0f.le_byte 0 4 0) with 0 in HA by (vm_compute; reflexivity). exact HA. }
  eapply SRr_bind.
  { eapply (aj_gx_entry_at B LAWS G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
      (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
      (fun _ mem' => val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 16)
      W regs mem LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 md k (F - sp0) _ HG eq_refl HJ
      ltac:(rewrite Hsp; lia) Ho16 ltac:(lia) ltac:(unfold ESTACK; lia)
      ltac:(unfold ESTACK, LLVMF_STK; lia) R3 R4 Q1
      (ret_ok_codeptr_v A_dr_r1 ltac:(unfold A_dr_r1, AF_arm_drain; lia) eq_refl)).
    - intros a. lia.
    - intros a Hwa _. exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 0 a LK4 ltac:(cbn; lia)).
    - intros a Hwa HnG. exfalso. apply HnG. apply HGlock. lia.
    - intros HPRE2 HSC2.
      exact (ALOCK ly3 S3 W regs mem _ (rg_lock fr_RG) 0 HPRE2
        Q10 ltac:(lia) ltac:(rewrite VLK; reflexivity) ltac:(lia) AVL eq_refl LK4
        ltac:(intros a Ha; split;
              [ destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [Hlt | Hge];
                [ exact (dj_av_ne W mem (rg_lock fr_RG) 4%nat 0 a LK0 ltac:(cbn; lia))
                | exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 0 a LK4 ltac:(cbn; lia)) ]
              | rewrite Hsp; unfold ESTACK in *; lia ])
        ltac:(intros a Ha; split;
              [ replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; exact (LKW (a - rg_lock fr_RG) ltac:(lia))
              | split; [ apply HNOWN; lia | rewrite Hsp; unfold ESTACK in *; lia ] ])). }
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJa & HPa & Hlk2 & Hfra & Hpresa).
  assert (KL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
      ~ (F - ESTACK <= a < F) -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha H1 H2; apply Hfra; [exact Ha | exact H1 | replace (sp0 + (F - sp0)) with F by lia; exact H2]).
  assert (HKY : Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m))
    by (apply Forall_forall; intros e _; apply dr_keys_le).
  pose proof (dj_ne_lockstep ly3 S3 W mem md mem2 m false true F HAR HKY (dj_ne_of_at ly3 S3 W mem m HMOD) KL
                ltac:(unfold ESTACK in *; lia) Hlk2) as HNE2.
  destruct (dj_ctx_lockstep cx m FF (flag_addr ly3 1 fpos) ly3 S3 W mem md mem2 HB HAR
              (ex_intro _ fpos (conj Hfin eq_refl))
              (conj HFR (conj HFL (conj HIN (conj HRV (conj HROM SVN))))) KL Hpresa) as (HCTX2 & HAT2).
  apply SRr_ret.
  exists regs2, mem2, md2, k. split; [reflexivity|].
  split.
  { assert (P23 : getr regs2 23 = w64 (rg_lock fr_RG))
      by (rewrite (dj_pres regs regs2 23%bv HPa ltac:(dj_cs)); exact Q23).
    exact (dcF_regs_kept cx t m j si FF (rg_lock fr_RG) (rg_lock fr_RG) regs regs2
             (dcF_pres_K regs regs2 HPa) P23 (conj HREGS Q23)). }
  split; [exact HJa|]. split; [reflexivity|].
  split; [exact HCTX2|]. split; [exact (HAT2 0 S192)|].
  split; [exact HNE2|]. split; [exact HSEP | exact HKY].
Qed.

(* ---- stage C: 0x8490c mv a0,s7 ; li s7,1 ; jal pthread_mutex_unlock -> 0x84918.
   Contract: lib/B/W_sites.v:105 aunlock_realizes at SIGMA WS_pthread_mutex_unlock (dre_AUNLOCK);
   journal composition: lib/B/W_sites.v:392 aj_gx_entry_at.  s7 leaves holding 1 (what lregs_common asks at
   the latch); image A reloads &g_lock from the frame cell F+40 here, B has it in s7 already. ---- *)
Lemma dc_stC : forall cx t m j si fpos FF ly S mc W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  dc_at cx t m j si fpos FF A_dr_r2 ly S mc true 0 (rg_lock fr_RG) W c ->
  SRr segs W c (dc_at cx t m j si fpos FF A_dr_r3 ly S mc false 0 1).
Proof.
  intros cx t m j si fpos FF ly S mc W c HB
    (regs & mem & md & k & -> & HR & HJ & HFF & HCTX & SAT & HNE & HSEP & HKB).
  pose proof HR as (HREGS & R23).
  pose proof HREGS as (R2 & R8 & R9 & R18 & R19 & R24 & R26 & R27 & R3 & R4 & R25 & Ht & R20 & R21 & R22).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  destruct (dcF_F cx HB) as (HFb & HF32 & Ho16 & Hsp0 & Hnlen).
  assert (HAR : AR segs B ly S W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof (dcF_fin cx fpos ly S W mem md k HJ) as Hfin.
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  assert (VLK : rg_lock fr_RG = 0x5d9040) by reflexivity.
  pose proof HNE as (_ & _ & _ & _ & _ & HLOCK & _).
  pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
  assert (HNOWN : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ aowned B ly S a).
  { intros a Ha Ho. destruct (HG a (HGlock a Ha)) as (Hi & Hno & _).
    apply Hno. exact (proj1 (al_owned_image _ _ LAWS ly S W mem _ a HAR Hi) Ho). }
  (* 0x8490c-0x84910: mv a0,s7 ; li s7,1 *)
  destruct (dc_plain_entry A_dr_r2 W regs mem R27) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  clear HE.
  paj_run_tok RUN HS HJ SHOK DRspan.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok segs _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (23%bv : bv 5) Q23.
  rewrite (EEo 23%nat 23%bv eq_refl), R23 in Q10.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dr_r3)) by exact Q1.
  assert (Q23' : getr regs1 23 = w64 1) by exact Q23.
  eapply SRr_bind.
  { eapply (aj_gx_entry_at B LAWS G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
      (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
      (fun regs' mem' => getr regs' 10 = w64 0 /\ val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 0)
      W regs1 mem LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly S md1 k (F - sp0) _ HG eq_refl HJ
      ltac:(rewrite Hsp1; lia) Ho16 ltac:(lia) ltac:(unfold ESTACK; lia)
      ltac:(unfold ESTACK, LLVMF_STK; lia)
      ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3) ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4) Q1'
      (ret_ok_codeptr_v A_dr_r3 ltac:(unfold A_dr_r3, AF_arm_drain; lia) eq_refl)).
    - intros a. lia.
    - intros a Hwa _. exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 16 a LK4 ltac:(cbn; lia)).
    - intros a Hwa HnG. exfalso. apply HnG. apply HGlock. lia.
    - intros HPRE2 HSC2.
      exact (AUNLOCK ly S W regs1 mem md1 (rg_lock fr_RG) HPRE2 Q10 ltac:(lia)
        ltac:(rewrite VLK; reflexivity) ltac:(lia) LK0 LK4 LK8
        ltac:(intros a Ha; split;
              [ destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [Hlt | Hge];
                [ exact (dj_av_ne W mem (rg_lock fr_RG) 4%nat 0 a LK0 ltac:(cbn; lia))
                | destruct (Z_lt_le_dec a (rg_lock fr_RG + 8)) as [Hlt2 | Hge2];
                  [ exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 16 a LK4 ltac:(cbn; lia))
                  | exact (dj_av_ne W mem (rg_lock fr_RG + 8) 4%nat 0 a LK8 ltac:(cbn; lia)) ] ]
              | rewrite Hsp1; unfold ESTACK in *; lia ])
        ltac:(intros a Ha; split;
              [ replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; exact (LKW (a - rg_lock fr_RG) ltac:(lia))
              | split; [ apply HNOWN; lia | rewrite Hsp1; unfold ESTACK in *; lia ] ])). }
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJa & HPa & (Ha0 & Hlk2) & Hfra & Hpresa).
  assert (KL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
      ~ (F - ESTACK <= a < F) -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha H1 H2; apply Hfra; [exact Ha | exact H1 | replace (sp0 + (F - sp0)) with F by lia; exact H2]).
  pose proof (dj_ne_lockstep ly S W mem md mem2 mc true false F HAR HKB HNE KL
                ltac:(unfold ESTACK in *; lia) Hlk2) as HNE2.
  destruct (dj_ctx_lockstep cx m FF (flag_addr ly 1 fpos) ly S W mem md mem2 HB HAR
              (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX KL Hpresa) as (HCTX2 & HAT2).
  apply SRr_ret.
  exists regs2, mem2, md2, k. split; [reflexivity|].
  split.
  { assert (P23 : getr regs2 23 = w64 1)
      by (rewrite (dj_pres regs1 regs2 23%bv HPa ltac:(dj_cs)); exact Q23').
    exact (dcF_regs_kept cx t m j si FF (rg_lock fr_RG) 1 regs regs2
             (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HPa r Hr) (KR r Hr)) P23 HR). }
  split; [exact HJa|]. split; [exact HFF|].
  split; [exact HCTX2|]. split; [exact (HAT2 0 SAT)|].
  split; [exact HNE2|]. split; [exact HSEP | exact HKB].
Qed.

(* ---- stage D: 0x84918 mv a0,s5 ; jal check_no_loss_read -> 0x84920.
   Contract: lib/B/W_contract.v:484 cnlr_spec at BASE + AF_fr_check_no_loss_read (dre_CNLR); its aleaf_post gained
   errno's view as its last conjunct (:112), which this stage does not need;
   journal composition: dr_callZ above (W_journal.v ajournal_gx_sub). ---- *)
Lemma dc_stD : forall cx t m j si fpos FF ly S mc h1 W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (si < 4)%nat -> nth si (lm_hs mc) None = Some h1 -> hl_recs (hs_pending h1) = [] ->
  dc_at cx t m j si fpos FF A_dr_r3 ly S mc false 0 1 W c ->
  SRr segs W c (dc_at cx t m j si fpos FF A_dr_r4 ly S mc false 0 1).
Proof.
  intros cx t m j si fpos FF ly S mc h1 W c HB Hsi Hh1 Hpend
    (regs & mem & md & k & -> & HR & HJ & HFF & HCTX & SAT & HNE & HSEP & HKB).
  pose proof HR as (HREGS & R23).
  pose proof HREGS as (R2 & R8 & R9 & R18 & R19 & R24 & R26 & R27 & R3 & R4 & R25 & Ht & R20 & R21 & R22).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (dcF_F cx HB) as (HFb & HF32 & Ho16 & Hsp0 & Hnlen).
  pose proof (dcF_fin cx fpos ly S W mem md k HJ) as Hfin.
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (VS : rg_s fr_RG = 0x5d8e60) by reflexivity.
  pose proof HNE as (_ & HSL & _).
  pose proof (HSL si Hsi) as HSLi. rewrite Hh1 in HSLi.
  destruct HSLi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _).
  destruct HPL as (_ & HPn & _).
  assert (HV0 : val_mem segs (mrestrict (w_H W) mem) (HA + 24) 4 0).
  { replace (HA + 24) with (HA + 16 + 8) by lia. unfold hl_n in HPn. rewrite Hpend in HPn. exact HPn. }
  assert (HPm : HA mod 16 = 0).
  { unfold HA. rewrite VS. unfold ASRC.
    replace (0x5d8e60 + 96 * Z.of_nat si) with ((0x5d8e6 + 6 * Z.of_nat si) * 16) by lia. apply Z_mod_mult. }
  assert (HAZ : azs B HA 28) by (apply (dcF_azs_sub _ _ _ _ HZS); unfold HA, ASRC; lia).
  destruct HAP as (HAP0 & HAP30).
  (* 0x84918: mv a0,s5 ; jal check_no_loss_read *)
  destruct (dc_plain_entry A_dr_r3 W regs mem R27) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  clear HE.
  paj_run_to_tok RUNTO HS HJ SHOK DRspan AF_fr_check_no_loss_read.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (23%bv : bv 5) Q23.
  rewrite (EEo 21%nat 21%bv eq_refl), R21 in Q10.
  rewrite (EEo 23%nat 23%bv eq_refl), R23 in Q23.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dr_r4)) by exact Q1.
  destruct (dr_afn_pre_at cx ly S fpos k W mem md1 regs1 CNLR_STK HB HJ
              ltac:(rewrite HFF; exact (proj1 HCTX)) Hsp1
              ltac:(rewrite Q1'; exact (ret_ok_codeptr_v A_dr_r4 ltac:(unfold A_dr_r4, AF_arm_drain; lia) eq_refl))
              ltac:(unfold raZ; rewrite Q1', unsigned_lit_small; unfold A_dr_r4, AF_arm_drain; lia)
              ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
              ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
              ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
              ltac:(unfold CNLR_STK; lia) ltac:(unfold CNLR_STK, LLVMF_STK; lia)) as (ch & HPRE1).
  eapply SRr_mono.
  { eapply (dr_callZ G_fr W regs1 mem (Z_to_bv 64 (BASE + AF_fr_check_no_loss_read)) LLVMF_STK sp0
      (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S md1 k CNLR_STK [] 0 []
      (F - sp0) (Z_to_bv 64 (BASE + A_dr_r4)) ch
      (fun ly2 S2 W2 _ mem2 md2 => ly2 = ly /\ S2 = S /\ ajournal segs B CNLR_STK F [] ly S W mem md1 [] ly S W2 mem2 md2 0)
      HG HJ ltac:(rewrite Hsp1; lia) ltac:(lia) ltac:(unfold CNLR_STK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
      ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) Q1' HPRE1).
    - eapply SRr_mono;
        [exact (CNLR W ly S regs1 mem md1 ch HA 0 HPRE1 Q10 HPm ltac:(unfold HA, ASRC; lia)
                  ltac:(unfold HA, ASRC; lia) HAZ ltac:(unfold HA, ASRC in *; lia) ltac:(unfold HA, ASRC in *; lia)
                  HV0 ltac:(lia) ltac:(left; reflexivity))|].
      cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & _).
      rewrite Hsp1 in HJc.
      exists ly, S, regs2, mem2, md2, 0.
      split; [rewrite Q1'; reflexivity|].
      split; [rewrite Hsp1; apply (ajournal_gx_G_mono segs B [] G_fr);
              [intros a Ha; exfalso; exact (inG_nil a Ha) | apply ajournal_gx_nil; exact HJc]|].
      split; [exact HP2|]. split; [reflexivity|]. split; [reflexivity|]. exact HJc.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HP2 & (-> & -> & HJp)).
  pose proof (dj_ne_plain ly S W W2 mem mem2 md1 md2 mc false CNLR_STK F HJp
                ltac:(unfold CNLR_STK; pose proof dr_ceil_lo; lia) HKB HNE) as HNE2.
  destruct (dj_ctx_plain cx m FF (flag_addr ly 1 fpos) ly S W W2 mem mem2 md1 md2 CNLR_STK HB HJp
              ltac:(unfold CNLR_STK; lia) (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX) as (HCTX2 & HAT2).
  exists regs2, mem2, md2, (k + k1).
  split; [reflexivity|].
  split.
  { assert (P23 : getr regs2 23 = w64 1)
      by (rewrite (dj_pres regs1 regs2 23%bv HP2 ltac:(dj_cs)); exact Q23).
    exact (dcF_regs_kept cx t m j si FF 1 1 regs regs2
             (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HP2 r Hr) (KR r Hr)) P23 HR). }
  split; [exact HJ2|]. split; [exact HFF|].
  split; [exact HCTX2|]. split; [exact (HAT2 0 SAT)|].
  split; [exact HNE2|]. split; [exact HSEP | exact HKB].
Qed.

(* ---------------- stage B's kit (dcB_) ---------------- *)
(* every block the representation names has a positive size *)
Lemma dcB_pos_alist : forall ly S (W : world segs) mem LA l lines b,
  alist_at B ly S W mem LA l lines -> In b (alist_blks l) -> 0 < snd b.
Proof.
  intros ly S W mem LA l lines b (_ & _ & _ & _ & _ & H6 & _) Hb. unfold alist_blks in Hb.
  apply in_app_or in Hb as [Hb | Hb].
  - destruct (hl_cap l =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
    destruct Hb as [<- | []]. cbn [snd]. destruct H6 as [(Hc & _) | (Hc & _)]; [lia|]. unfold AREC. lia.
  - apply in_map_iff in Hb as (r & <- & _). cbn [snd]. lia.
Qed.
Lemma dcB_pos_asrc : forall ly S (W : world segs) mem HA h b,
  asrc_at B ly S W mem HA h -> In b (asrc_blks h) -> 0 < snd b.
Proof.
  intros ly S W mem HA h b
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H22 & H23 & _) Hb.
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [cbn [snd]; unfold APARTIAL; lia|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (dcB_pos_alist _ _ _ _ _ _ _ _ H10 Hb)|].
  apply in_app_or in Hb as [Hb | Hb];
    [exact (dcB_pos_alist _ _ _ _ _ _ _ _ H22 Hb) | exact (dcB_pos_alist _ _ _ _ _ _ _ _ H23 Hb)].
Qed.
Lemma dcB_pos_aentry : forall ly S (W : world segs) mem e b,
  aentry_ok B ly S W mem e -> In b (aentry_blks e) -> 0 < snd b.
Proof.
  intros ly S W mem e b (_ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _ & K12 & _ & _ & _) Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (re_cap e =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
    destruct Hb as [<- | []]. cbn [snd]. destruct K10 as [(Hc & _) | (Hc & _)]; lia.
  - apply in_app_or in Hb as [Hb | Hb].
    + destruct (re_hp e =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
      destruct Hb as [<- | []]. cbn [snd]. destruct K12 as [(Hz & _) | (_ & _ & _ & Hk & _)]; lia.
    + apply in_map_iff in Hb as (kk & <- & _). cbn [snd]. lia.
Qed.
Lemma dcB_pos_aout : forall ly S (W : world segs) mem c O mx no cap out b,
  aout_at B fr_RG ly S W mem c O mx no cap out -> In b (aout_blks cap out) -> 0 < snd b.
Proof.
  intros ly S W mem c O mx no cap out b HO Hb.
  pose proof HO as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& Hblk).
  unfold aout_blks in Hb. destruct (cap =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
  destruct Hb as [<- | []]. cbn [snd]. destruct Hblk as [(Hc & _) | (Hc & _)]; lia.
Qed.
(* drain's G is inside the entry's; ROM is outside it; the cells amodel_ne keeps beside it are outside it *)
Lemma dcB_GDR_ok : gx_ok segs B (G_DR B fr_RG).
Proof. intros a Ha. exact (HG a (HG_DR a Ha)). Qed.
Lemma dcB_rom_out : rom_out segs B (G_DR B fr_RG).
Proof.
  intros a Ha. destruct (DR_ROM_OUT a Ha) as (H1 & H2 & H3 & H4).
  split; [intros HGa; exact (H1 (HG_DR a HGa))|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.
Lemma dcB_GK_out : forall a, inG DR_GK a \/ rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
  ~ inG (G_DR B fr_RG) a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha.
  unfold inG, DR_GK, G_DR, G_SL in *. rewrite !Exists_cons, Exists_nil in *.
  unfold in_zr in *. cbn [fst snd] in *. dt_num.
Qed.
(* a model block of the call's footprint is the entry's footprint's or new since the entry *)
Lemma dcB_fp_blk : forall cx m ly S b a,
  ablocks_sep B fr_FP cx m ly S -> In b (model_blks m) -> fst b <= a < fst b + req_size (snd b) ->
  (inFP (lf_FP fr_FP cx) a /\ exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
  in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly S) a.
Proof.
  intros cx m ly S [p n] a ((rest & HP) & H2) Hb Ha. cbn [fst snd] in Ha.
  assert (HbL : In (p, n) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
  destruct (in_dec dc_dec (p, n) (ablocks B (c_ly cx) (c_S cx))) as [Hin | Hnin].
  - left. split; [|exists p, n; split; [exact HbL | exact Ha]].
    destruct (H2 _ Hb) as [Hc | Hc]; [exfalso; exact (Hc Hin) | exact (Hc a Ha)].
  - right. exists p, n. split; [exact HbL|]. split; [exact Hnin | exact Ha].
Qed.
(* a byte outside drain's footprint dr_fp SA e h cap out = (SA, SA + AENT) :: ablocks_fp X *)
Lemma dcB_nfp : forall G SA (X : list (Z * Z)) a,
  G <= SA -> SA + AENT <= G + ATABLE ->
  ~ (G <= a < G + ATABLE /\ SA <= a < SA + AENT) ->
  (forall b, In b X -> ~ (fst b <= a < fst b + req_size (snd b))) ->
  ~ inFP ((SA, SA + AENT) :: ablocks_fp X) a.
Proof.
  intros G SA X a H1 H2 H3 H4 (r & Hr & Ha). destruct Hr as [<- | Hr].
  - cbn [fst snd] in Ha. apply H3. split; lia.
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hb). cbn [fst snd] in Ha. exact (H4 b Hb Ha).
Qed.
Lemma dcB_nfp_blk : forall ly S (W : world segs) mem md G SA X p0 n0 a,
  AR segs B ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + AENT <= G + ATABLE ->
  (forall b, In b X -> In b (ablocks B ly S)) ->
  In (p0, n0) (ablocks B ly S) -> ~ In (p0, n0) X -> p0 <= a < p0 + req_size n0 ->
  ((p0, n0) <> (G, ATABLE) \/ ~ (SA <= a < SA + AENT)) ->
  ~ inFP ((SA, SA + AENT) :: ablocks_fp X) a.
Proof.
  intros ly S W mem md G SA X p0 n0 a HAR HGin H1 H2 HXL Hb0 HnX Ha Hor.
  apply (dcB_nfp G); [exact H1 | exact H2 | |].
  - intros (Ht & Hs). destruct Hor as [Hne | Hn]; [|exact (Hn Hs)].
    apply (dj_apart ly S W mem md p0 n0 G ATABLE a HAR Hb0 HGin Hne Ha).
    replace (req_size ATABLE) with ATABLE by reflexivity. exact Ht.
  - intros [q r] Hb Hq. cbn [fst snd] in Hq.
    assert (Hne : (p0, n0) <> (q, r)) by (intros E; apply HnX; rewrite E; exact Hb).
    exact (dj_apart ly S W mem md p0 n0 q r a HAR Hb0 (HXL _ Hb) Hne Ha Hq).
Qed.
Lemma dcB_nfp_frm : forall ly S (W : world segs) mem md G SA X cid pos a,
  AR segs B ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + AENT <= G + ATABLE ->
  (forall b, In b X -> In b (ablocks B ly S)) -> In (cid, pos) (frames S) ->
  (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
  ~ inFP ((SA, SA + AENT) :: ablocks_fp X) a.
Proof.
  intros ly S W mem md G SA X cid pos a HAR HGin H1 H2 HXL Hfr Ha.
  assert (HNB : forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)).
  { intros p n Hin Hpa.
    destruct (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hfr) as (Hf0 & Hfc & _).
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
    pose proof (sep_block_frame segs B LAWS ly S W mem md p n cid pos HAR Hin Hfr) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
    pose proof (fs_frame_bytes_nonneg cid) as Hfb.
    pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(lia)) as Hs1.
    pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2.
    pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfb) as Hs3.
    unfold in_app, kLowShadowBeg in Happ.
    destruct Ha as [Ha | Ha]; lia. }
  apply (dcB_nfp G); [exact H1 | exact H2 | |].
  - intros (Ht & _). apply (HNB G ATABLE HGin). replace (req_size ATABLE) with ATABLE by reflexivity. exact Ht.
  - intros [q r] Hb Hq. exact (HNB q r (HXL _ Hb) Hq).
Qed.
(* a closed slot's 96 zero bytes read 0 in any 4-byte field *)
Lemma dcB_zero_vm : forall (mm : word -> option byte) a N o,
  garr8 segs mm a (repeat 0 N) -> 0 <= o -> o + 4 <= Z.of_nat N -> val_mem segs mm (a + o) 4 0.
Proof.
  intros mm a N o Hg Ho HN kk Hk.
  destruct (Hg (Z.to_nat o + kk)%nat ltac:(rewrite repeat_length; lia)) as [Hv _].
  specialize (Hv 0%nat ltac:(lia)). rewrite nth_repeat in Hv.
  replace (a + o + Z.of_nat kk) with (a + Z.of_nat (Z.to_nat o + kk) + Z.of_nat 0) by lia.
  rewrite Hv. do 4 (destruct kk as [|kk]; [reflexivity|]). lia.
Qed.
(* the relay's table in memory: entry j as a byte array, and the table after entry j is rewritten *)
Lemma dr_pads_of_relay : forall ly S W mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es /\
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es.
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & HE & _).
  split; rewrite Forall_forall in HE |- *; intros e He;
    destruct (HE e He) as (_ & _ & H3 & H4 & H5 & _); [split; assumption | exact H5].
Qed.
Lemma dr_tbl_entry : forall (W : world segs) (mem : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (j : nat),
  atable_at W mem G es tail -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (j < length es)%nat ->
  garr8 segs (arm W mem) (G + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es dr_e0))).
Proof.
  intros W mem G es tail j (_ & _ & Hg) Hpad Hj.
  destruct (dra_len_split rentry es j Hj) as [Hfl _].
  assert (HX : length (bzs (concat (map entry_bytes (firstn j es)))) = (56 * j)%nat).
  { rewrite dra_bzs_length, concat_entry_length, Hfl by (apply dra_Forall_firstn; exact Hpad). reflexivity. }
  rewrite (dra_concat_split _ _ entry_bytes es j dr_e0 Hj) in Hg. rewrite !dra_bzs_app in Hg.
  apply garr8_app in Hg as [Hg1 _]. apply garr8_app in Hg1 as [_ Hg2]. apply garr8_app in Hg2 as [Hg3 _].
  rewrite HX in Hg3. replace (G + AENT * Z.of_nat j) with (G + Z.of_nat (56 * j)) by (unfold AENT; lia).
  exact Hg3.
Qed.
Lemma dr_awr_of_garr8 : forall ly S (W : world segs) mem md p n a (l : list Z),
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a -> a + Z.of_nat (length l) <= p + req_size n ->
  garr8 segs (arm W mem) a l -> awr W mem a (Z.of_nat (length l)).
Proof.
  intros ly S W mem md p n a l HAR Hin Hp Hq _ i Hi. unfold arm. apply (apresent_writable segs).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & Hpr & _).
  exact (proj1 (Hpr (a + i) ltac:(lia))).
Qed.
Lemma dr_tbl_upd : forall (W W' : world segs) (mem mem' : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (j : nat) (e' : rentry),
  atable_at W mem G es tail ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  length (re_pad1 e') = 4%nat -> length (re_pad2 e') = 4%nat ->
  (j < length es)%nat ->
  garr8 segs (arm W' mem') (G + AENT * Z.of_nat j) (bzs (entry_bytes e')) ->
  (forall a, G <= a < G + ATABLE -> ~ (G + AENT * Z.of_nat j <= a < G + AENT * Z.of_nat j + AENT) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  atable_at W' mem' G (set_nth j e' es) tail.
Proof.
  intros W W' mem mem' G es tail j e' (Htl & Htot & Hg) Hpad Hp1 Hp2 Hj Hge Hview.
  assert (Hall : forall y, In y es -> length (re_pad1 y) = 4%nat /\ length (re_pad2 y) = 4%nat)
    by (apply Forall_forall; exact Hpad).
  assert (Hpad' : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (set_nth j e' es)).
  { apply Forall_forall. intros y Hy. cbv beta. destruct (dr_in_set_nth rentry j e' y es Hy) as [-> | Hy'].
    - split; assumption.
    - apply Hall. exact (dr_in_rm rentry j y es Hy'). }
  rewrite length_app, (concat_entry_length es Hpad) in Htot.
  destruct (dra_len_split rentry es j Hj) as [Hfl Hsl].
  assert (HX : length (bzs (concat (map entry_bytes (firstn j es)))) = (56 * j)%nat).
  { rewrite dra_bzs_length, concat_entry_length, Hfl by (apply dra_Forall_firstn; exact Hpad). reflexivity. }
  assert (HZ : length (bzs (concat (map entry_bytes (skipn (S j) es)))) = (56 * (length es - S j))%nat).
  { rewrite dra_bzs_length, concat_entry_length, Hsl by (apply dra_Forall_skipn; exact Hpad). reflexivity. }
  assert (HE0 : length (bzs (entry_bytes (nth j es dr_e0))) = 56%nat).
  { assert (Hin : In (nth j es dr_e0) es) by (apply nth_In; exact Hj).
    destruct (Hall _ Hin) as [H1 H2]. rewrite dra_bzs_length. apply entry_bytes_length; assumption. }
  assert (HE' : length (bzs (entry_bytes e')) = 56%nat)
    by (rewrite dra_bzs_length; apply entry_bytes_length; assumption).
  pose proof (dra_bzs_length tail) as HT.
  assert (Hfr : forall a, G <= a < G + ATABLE -> ~ (G + AENT * Z.of_nat j <= a < G + AENT * Z.of_nat j + AENT) ->
     mbyte segs (arm W' mem') a = mbyte segs (arm W mem) a).
  { intros a Ha Hn. unfold arm. apply mbyte_of_aview. exact (Hview a Ha Hn). }
  split; [rewrite set_nth_length; exact Htl|].
  split; [rewrite length_app, (concat_entry_length _ Hpad'), set_nth_length; exact Htot|].
  rewrite (dra_concat_set_split _ _ entry_bytes es j e' Hj).
  rewrite (dra_concat_split _ _ entry_bytes es j dr_e0 Hj) in Hg.
  rewrite !dra_bzs_app in Hg |- *.
  apply garr8_app in Hg as [Hg1 HgT]. apply garr8_app in Hg1 as [HgX Hg2]. apply garr8_app in Hg2 as [_ HgZ].
  apply garr8_app. split; [apply garr8_app; split; [|apply garr8_app; split]|].
  - apply (garr8_frame segs _ _ G _ HgX). intros a Ha. apply Hfr; unfold ATABLE, AENT in *; lia.
  - replace (G + Z.of_nat (length (bzs (concat (map entry_bytes (firstn j es))))))
      with (G + AENT * Z.of_nat j) by (unfold AENT; lia).
    exact Hge.
  - rewrite HE'. rewrite HE0 in HgZ. apply (garr8_frame segs _ _ _ _ HgZ). intros a Ha.
    apply Hfr; unfold ATABLE, AENT in *; lia.
  - rewrite !length_app, HE'. rewrite !length_app, HE0 in HgT. apply (garr8_frame segs _ _ _ _ HgT). intros a Ha.
    apply Hfr; unfold ATABLE, AENT in *; lia.
Qed.
(* the model's blocks the call does not touch *)
Definition dcB_CA (es : list rentry) (j : nat) : list (Z * Z) :=
  concat (map aentry_blks (firstn j es ++ skipn (S j) es)).
Definition dcB_CS (hs : list (option hsrc)) (si : nat) : list (Z * Z) :=
  concat (map slot_blks (firstn si hs ++ skipn (S si) hs)).
Definition dcB_T (cx : lfcx) (m : lmod) (j si : nat) (rest0 : list (Z * Z)) : list (Z * Z) :=
  dcB_CA (lm_es m) j ++ dcB_CS (lm_hs m) si ++ input_blks cx ++ rest0.
(* dr_post without the return configuration, the composed journal at G_fr and the callee-saved registers *)
Definition dcB_post (regs : bvmap 5 word) ly S (W : world segs) (mem : word -> option byte) (md : Model)
  (SA HA : Z) (e : rentry) (h : hsrc) (c : ctl) (O : list byte) (mx no cap out : Z)
  (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  : Prop :=
exists k (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) rest,
let fin := dr_fin c mx no cap e h in
let live := dr_live c h in
let cap' := if live then drain_b_c.ds_ocap fin else cap in
ajournal_gx segs B (G_DR B fr_RG) 0 [] DRAIN_STK (spZ regs) (dr_fp SA e h cap out) ly S W mem md [] ly' S' W' mem' md' k /\
apres_kept B W mem W' mem' /\
mo_le MT S S' (dr_cost MT c mx no cap e h) /\
Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) /\
Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) /\
garr8 segs (arm W' mem') SA (bzs (entry_bytes e')) /\ awr W' mem' SA AENT /\ aentry_ok B ly' S' W' mem' e' /\
Z.of_nat (length (re_keys e')) <= re_nheld e' /\
re_fd e' = re_fd e /\ re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\ 0 < re_cap e' /\
re_cap e' = drain_b_c.ds_cap fin /\ bzs (re_U e') = drain_b_c.ds_u fin /\
re_skip e' = (if drain_b_c.ds_skip fin then 1 else 0) /\
drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
NoDup (drain_b_c.keys_texts (re_keys e')) /\
same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
asrc_at B ly' S' W' mem' HA h' /\
(forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> ~ (HA <= a < HA + ASRC) -> abyte_kept W mem W' mem' a) /\
hl_cap (hs_expected h') = drain_b_c.ds_ecap fin /\
hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))) /\
hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
hs_partial h' = hs_partial h /\
hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
hs_held h' = hs_held h /\
re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
bzs LB = with_nul (dr_lines h) /\
aout_at B fr_RG ly' S' W' mem' (dr_ctl c h ev') (if live then O ++ LB else O) mx (if live then no + dr_tot h else no) cap' out'.
Lemma dcB_post_of : forall regs ly S (W : world segs) mem md SA HA e h c O mx no cap out (W' : world segs) c',
  dr_post B MT fr_RG regs ly S W mem md SA HA e h c O mx no cap out W' c' ->
  exists ly' S' regs' mem' md' k, c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    ajournal_gx segs B G_fr 0 [] DRAIN_STK (spZ regs) (dr_fp SA e h cap out) ly S W mem md [] ly' S' W' mem' md' k /\
    aregs_preserved regs regs' /\
    dcB_post regs ly S W mem md SA HA e h c O mx no cap out ly' S' W' regs' mem' md'.
Proof.
  intros regs ly S W mem md SA HA e h c O mx no cap out W' c'
    (ly' & S' & regs' & mem' & md' & k & e' & h' & out' & ev' & LB & rest & HP).
  cbv zeta in HP. destruct HP as (Hc & HJ & HPR & HAPK & HMO & HP1 & HP2 & HG8 & HAW & HEOK & REST).
  exists ly', S', regs', mem', md', k. split; [exact Hc|].
  split; [exact (ajournal_gx_G_mono segs B (G_DR B fr_RG) G_fr 0 [] DRAIN_STK (spZ regs) _ ly S W mem md [] ly' S' W' mem' md'
                   k HG_DR HJ)|].
  split; [exact HPR|].
  exists k, e', h', out', ev', LB, rest. cbv zeta. split; [exact HJ|].
  exact (conj HAPK (conj HMO (conj HP1 (conj HP2 (conj HG8 (conj HAW (conj HEOK (conj (dr_keys_le e') REST)))))))).
Qed.
(* drain's functional values do not read the stream's errno value (dc_ctl's last field) *)
Lemma dcB_live_ctl : forall c ev h, dr_live (dc_ctl c ev) h = dr_live c h.
Proof. reflexivity. Qed.
Lemma dcB_fin_ctl : forall c ev mx no cap e h, dr_fin (dc_ctl c ev) mx no cap e h = dr_fin c mx no cap e h.
Proof. intros. unfold dr_fin. rewrite dcB_live_ctl. reflexivity. Qed.
Lemma dcB_tr_ctl : forall c ev mx no cap e h, dr_tr (dc_ctl c ev) mx no cap e h = dr_tr c mx no cap e h.
Proof. intros. unfold dr_tr. rewrite dcB_live_ctl. reflexivity. Qed.
Lemma dcB_cost_ctl : forall c ev mx no cap e h, dr_cost MT (dc_ctl c ev) mx no cap e h = dr_cost MT c mx no cap e h.
Proof. intros. unfold dr_cost. rewrite dcB_tr_ctl. reflexivity. Qed.
Lemma dcB_dctl_ctl : forall c ev h ev', dr_ctl (dc_ctl c ev) h ev' = dc_ctl (dr_ctl c h ev') ev'.
Proof. reflexivity. Qed.
(* a byte of one of DR_GK's cells (the cell's range is the hypothesis H) *)
Ltac dcB_gk H := left; unfold inG, DR_GK;
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - H; lia | apply Exists_cons_tl]).

(* ---- stage B: 0x84904 mv a0,s6 ; jal drain -> 0x8490c.
   Contract: lib/B/W_contract.v:1027 dr_spec at BASE + AF_fr_drain (dre_DRAIN);
   journal composition: dr_callZ above (W_journal.v ajournal_gx_sub, then ajournal_gx_G_mono from drain's
   G_DR to the entry's G_fr in dcB_post_of). ---- *)
Lemma dc_stB : forall cx t m j si h fpos FF ly S W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  dc_static cx t m j si h -> LS cx t m ly S ->
  dc_at cx t m j si fpos FF A_dr_r1 ly S m true 0 (rg_lock fr_RG) W c ->
  SRr segs W c (fun W' c' => exists ly' S' e' h' out' ev' LB,
    dc_at cx t m j si fpos FF A_dr_r2 ly' S' (dr_m1 m j si h h' e' ev' LB out') true 0 (rg_lock fr_RG) W' c' /\
    mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) /\
    dr_dfun m si h j e' h' LB).
Proof.
  intros cx t m j si h fpos FF ly S W c HB (Hatop & Hpick & Hj & Hfdj & Hef0 & HRI) HLS
    (regs & mem & md & k & -> & HR & HJ & HFFe & HCTX & S192 & HNE & HSEP & HKY).
  pose proof HR as (HREGS & R23).
  pose proof HREGS as (R2 & R8 & R9 & R18 & R19 & R24 & R26 & R27 & R3 & R4 & R25 & Ht & R20 & R21 & R22).
  pose proof HCTX as (HFR & HFL & HIN & HRV & HJT & SVN).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : AR segs B ly S W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof HNE as (Hlen4 & HSL & HREL & (ev0 & HOUT) & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  destruct (dcF_F cx HB) as (HFb & HF32 & Ho16 & Hsp0 & Hnlen).
  pose proof (dcF_fin cx fpos ly S W mem md k HJ) as Hfin.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (Hsp : spZ regs = lf_F cx)
    by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  (* ---- 0x84904: mv a0,s6 ; jal drain ---- *)
  destruct (dc_plain_entry A_dr_r1 W regs mem R27) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  clear HE.
  paj_run_to_tok RUNTO HS HJ SHOK DRspan AF_fr_drain.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR3.
  cbn [ms_regs restrict] in KR3.
  prreg HS (1%bv : bv 5) Q1d. prreg HS (10%bv : bv 5) Q10d. prreg HS (23%bv : bv 5) Q23d.
  rewrite (EEo 22%nat 22%bv eq_refl), R22 in Q10d.
  rewrite (EEo 23%nat 23%bv eq_refl), R23 in Q23d.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (mdD := with_vm_backing (m_vm_lazy md) mat md) in *.
  assert (HspD : spZ (ms_regs ms) = lf_F cx) by (unfold spZ; rewrite (KR3 2%bv ltac:(dc_in)); exact Hsp).
  assert (HGONE0 : forall p n i, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> ~ In (p, n) (ablocks B ly S) ->
      0 <= i < req_size n -> inFP (lf_FP fr_FP cx) (p + i)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _).
    pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hg & _). exact Hg. }
  (* ---- drain's premises ---- *)
  pose proof Hpick as (_ & Hsi4 & Hhsi).
  destruct (dr_pads_of_relay ly S W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS).
  pose proof HREL as (RL1 & RL2 & RL3 & RL4 & RL5 & RL6 & RL7 & HGin & (tl & HTAB) & HENT & HNDF & HETB).
  assert (HEOK : aentry_ok B ly S W mem (nth j (lm_es m) dr_e0))
    by (rewrite Forall_forall in HENT; apply HENT, nth_In; exact Hj).
  destruct (RI_pair cx t m si h j HRI Hpick Hj Hfdj Hef0) as (HSK & HSKU & _ & _).
  destruct (dr_blk ly S W mem md (lm_G m) ATABLE HAR HGin) as (HG4096 & HGceil & _).
  assert (HSA : lm_G m <= lm_G m + AENT * Z.of_nat j /\ lm_G m + AENT * Z.of_nat j + AENT <= lm_G m + ATABLE)
    by (unfold AENT, ATABLE; lia).
  (* dr_spec's entry-pointer alignment (lib/B/W_contract.v:1035, cand11): the table is a live block, so 16-aligned
     (al_blocks), and AENT = 56 is a multiple of 8 - the derivation of _drain_entry.v's HSA8 *)
  assert (HSA8 : (lm_G m + AENT * Z.of_nat j) mod 8 = 0).
  { destruct (al_blocks _ _ LAWS ly S W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & _).
    unfold AENT. pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
    rewrite D. replace (16 * (lm_G m / 16) + 56 * Z.of_nat j) with ((2 * (lm_G m / 16) + 7 * Z.of_nat j) * 8) by ring.
    apply Z_mod_mult. }
  assert (HSRC0 : asrc_at B ly S W mem (rg_s fr_RG + ASRC * Z.of_nat si) h).
  { pose proof (HSL si Hsi4) as Hs. rewrite Hhsi in Hs. exact Hs. }
  pose proof HSRC0 as (_ & _ & _ & _ & _ & _ & _ & _ & Hfdrng & _).
  pose proof (dr_tbl_entry W mem (lm_G m) (lm_es m) tl j HTAB HPAD Hj) as HEB.
  assert (HEL : length (bzs (entry_bytes (nth j (lm_es m) dr_e0))) = 56%nat).
  { pose proof HEOK as (_ & _ & Hq1 & Hq2 & _). rewrite dra_bzs_length. apply entry_bytes_length; assumption. }
  assert (HEW : awr W mem (lm_G m + AENT * Z.of_nat j) AENT).
  { pose proof (dr_awr_of_garr8 ly S W mem md (lm_G m) ATABLE (lm_G m + AENT * Z.of_nat j)
                  (bzs (entry_bytes (nth j (lm_es m) dr_e0))) HAR HGin ltac:(lia)
                  ltac:(rewrite HEL; replace (req_size ATABLE) with ATABLE by reflexivity; unfold AENT, ATABLE in *; lia)
                  HEB) as Hw.
    rewrite HEL in Hw. exact Hw. }
  assert (HOTH : aothers_at fr_RG W mem si (re_fd (nth j (lm_es m) dr_e0))).
  { intros i Hi Hne. pose proof (HSL i Hi) as Hs. revert Hs.
    destruct (nth i (lm_hs m) None) as [hi|] eqn:Ehi; intros Hs; cbn [aslot] in Hs.
    - exists (hs_fd hi), (hs_open hi). pose proof Hs as (V1 & V2 & _ & _ & _ & _ & _ & _ & Vfd & _).
      split; [exact V1|]. split; [exact V2|]. right. rewrite Hfdj.
      rewrite !Z.mod_small by lia.
      exact (RI_fds cx t m i si hi h HRI Hi Hsi4 Hne Ehi Hhsi).
    - exists 0, 0. destruct Hs as (Hz & _).
      pose proof (dcB_zero_vm _ _ (Z.to_nat ASRC) 0 Hz ltac:(lia)
                    ltac:(rewrite Z2Nat.id by (unfold ASRC; lia); unfold ASRC; lia)) as Hz0.
      rewrite Z.add_0_r in Hz0.
      split; [exact Hz0|]. split; [|left; reflexivity].
      exact (dcB_zero_vm _ _ (Z.to_nat ASRC) 4 Hz ltac:(lia)
               ltac:(rewrite Z2Nat.id by (unfold ASRC; lia); unfold ASRC; lia)). }
  assert (HXM : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      In b (model_blks m)).
  { intros b Hb. unfold model_blks. right. apply in_app_or in Hb as [Hb | Hb].
    - apply in_or_app. left. apply in_concat. exists (aentry_blks (nth j (lm_es m) dr_e0)).
      split; [apply in_map, nth_In; exact Hj | exact Hb].
    - apply in_or_app. right. apply in_app_or in Hb as [Hb | Hb].
      + apply in_or_app. left. apply in_concat. exists (slot_blks (Some h)). split; [|exact Hb].
        rewrite <- Hhsi. apply in_map, nth_In. lia.
      + apply in_or_app. right. exact Hb. }
  pose proof HSEP as HSEPc.
  destruct HSEP as ((rest0 & HP0) & HSEP2).
  assert (HXL : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP0)).
    apply in_or_app. right. apply in_or_app. left. exact (HXM b Hb). }
  assert (HXP : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      0 < snd b).
  { intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [exact (dcB_pos_aentry _ _ _ _ _ _ HEOK Hb)|].
    apply in_app_or in Hb as [Hb | Hb];
      [exact (dcB_pos_asrc _ _ _ _ _ _ _ HSRC0 Hb) | exact (dcB_pos_aout _ _ _ _ _ _ _ _ _ _ _ HOUT Hb)]. }
  unfold model_blks in HP0.
  pose proof (dr_concat_nth_perm _ _ aentry_blks (lm_es m) j dr_e0 Hj) as HCA.
  pose proof (dr_concat_nth_perm _ _ slot_blks (lm_hs m) si None ltac:(lia)) as HCS.
  rewrite Hhsi in HCS. cbn [slot_blks] in HCS.
  pose proof (dcB_perm_pre _ _ _ _ _ _ _ _ _ _ _ HP0 HCA HCS) as HPERM0.
  assert (HU : Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL)
    by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hu1 & Hu2 & _); lia).
  destruct (LS_drain_pre cx t m ly S si h j HLS HRI Hatop Hpick Hj Hfdj Hef0 Ht HU HXP) as (L1 & L2 & L3 & L4 & L5 & L6).
  rewrite <- (dcB_tr_ctl (lm_c m) ev0) in L4, L5. rewrite <- (dcB_cost_ctl (lm_c m) ev0) in L6.
  destruct (dr_afn_pre_at cx ly S fpos k W mem mdD (ms_regs ms) DRAIN_STK HB HJ) as (ch & HPRED).
  { rewrite HFFe. exact HFR. }
  { exact HspD. }
  { rewrite Q1d. apply ret_ok_codeptr_v; [unfold A_dr_r1, AF_arm_drain; lia | reflexivity]. }
  { unfold raZ. rewrite Q1d, unsigned_lit_small by (unfold A_dr_r1, AF_arm_drain; lia).
    unfold A_dr_r1, AF_arm_drain; lia. }
  { rewrite (KR3 3%bv ltac:(dc_in)). exact R3. }
  { rewrite (KR3 4%bv ltac:(dc_in)). exact R4. }
  { rewrite (KR3 8%bv ltac:(dc_in)). exact R8. }
  { unfold DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia. }
  { unfold DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK. lia. }
  (* ---- drain(r), composed into the function's journal ---- *)
  eapply SRr_mono.
  { apply (dr_callZ G_fr W (ms_regs ms) mem (Z_to_bv 64 (BASE + AF_fr_drain)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S mdD k DRAIN_STK
      (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m)) 0 []
      (lf_F cx - sp0) (Z_to_bv 64 (BASE + A_dr_r2)) ch
      (fun ly2 S2 W2 regs2 mem2 md2 => dcB_post (ms_regs ms) ly S W mem mdD (lm_G m + AENT * Z.of_nat j)
         (rg_s fr_RG + ASRC * Z.of_nat si) (nth j (lm_es m) dr_e0) h (dc_ctl (lm_c m) ev0) (lm_O m) (lm_mx m)
         (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) ly2 S2 W2 regs2 mem2 md2)
      HG HJ).
    - rewrite HspD. lia.
    - lia.
    - unfold DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK. lia.
    - lia.
    - lia.
    - intros a Ha. exfalso. exact (inFP_nil a Ha).
    - exact Q1d.
    - exact HPRED.
    - eapply SRr_mono.
      { exact (DRAIN W ly S (ms_regs ms) mem mdD ch (lm_G m) (lm_G m + AENT * Z.of_nat j)
                 (nth j (lm_es m) dr_e0) si h (dc_ctl (lm_c m) ev0) (lm_O m) (lm_mx m)
                 (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) HPRED Q10d HGin (proj1 HSA) (proj2 HSA) HSA8
                 HEB HEW HEOK Hsi4 HSRC0 HOTH (eq_sym Hfdj) HSK HSKU HOUT HRV (ex_intro _ _ HPERM0)
                 L1 L2 L3 L4 L5 L6). }
      cbv beta. intros W2 c2 _ HPOST.
      destruct (dcB_post_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST)
        as (ly2 & S2 & regs2 & mem2 & md2 & k2 & Hc2 & HJ2 & HPR2 & HK2).
      exists ly2, S2, regs2, mem2, md2, k2. rewrite Q1d in Hc2.
      split; [exact Hc2|]. split; [exact HJ2|]. split; [exact HPR2 | exact HK2].
    - intros a (r & Hr & Ha). destruct Hr as [<- | Hr].
      + cbn [fst snd] in Ha.
        apply (dcB_fp_blk cx m ly S (lm_G m, ATABLE) a HSEPc);
          [unfold model_blks; left; reflexivity
          | cbn [fst snd]; replace (req_size ATABLE) with ATABLE by reflexivity; unfold AENT, ATABLE in *; lia].
      + unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hb). cbn [fst snd] in Ha.
        exact (dcB_fp_blk cx m ly S b a HSEPc (HXM b Hb) Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HPR & HK).
  destruct HK as (k2 & e' & h' & out' & ev' & LB & rest & HK). cbv zeta in HK.
  destruct HK as (HJD & HPK & HMO & HP1 & HP2 & HN1 & HN2 & HN3 & HKE & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16
                  & D17 & D18 & D19 & HSRC & HGS & D22 & D23 & D24 & D25 & D26 & D27 & D28 & D29 & D30 & D31 & D32 & D33
                  & D34 & D35 & D36 & D37 & D38 & HOUT2).
  rewrite HspD in HJD.
  rewrite dcB_cost_ctl in HMO. rewrite dcB_fin_ctl in D12, D13, D14, D15, D16, D22.
  rewrite ?dcB_live_ctl, ?dcB_fin_ctl, ?dcB_dctl_ctl in HOUT2. rewrite ?dcB_live_ctl, ?dcB_fin_ctl in HP2.
  (* ---- the blocks across the call ---- *)
  pose proof dcB_GDR_ok as HGDR.
  pose proof (dj_nodup ly S W mem md HAR) as HNDS.
  assert (HAR2 : AR segs B ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR; exact HJD).
  pose proof (dj_nodup ly2 S2 W2 mem2 md2 HAR2) as HNDS2.
  assert (HP1' : Permutation (ablocks B ly S)
      ((aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ++ rest))
    by (rewrite <- !app_assoc; exact HP1).
  assert (HRT : Permutation rest ((lm_G m, ATABLE) :: dcB_T cx m j si rest0))
    by exact (dcB_perm_rest _ _ _ _ _ _ _ HPERM0 HP1).
  assert (KTR : forall b, In b (dcB_T cx m j si rest0) -> In b rest)
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HRT)); right; exact Hb).
  assert (KTL2 : forall b, In b rest -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)).
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb. }
  assert (HGr : In (lm_G m, ATABLE) rest) by (apply (Permutation_in _ (Permutation_sym HRT)); left; reflexivity).
  assert (HCSin : forall i hi b, (i < 4)%nat -> i <> si -> nth i (lm_hs m) None = Some hi -> In b (asrc_blks hi) ->
      In b (dcB_T cx m j si rest0)).
  { intros i hi b Hi Hne Ehi Hb. unfold dcB_T. apply in_or_app. right. apply in_or_app. left. unfold dcB_CS.
    apply in_concat. exists (slot_blks (Some hi)). split; [|exact Hb]. apply in_map. rewrite <- Ehi.
    apply dc_in_rm_nth; lia. }
  assert (HCAin : forall y b, In y (firstn j (lm_es m) ++ skipn (Datatypes.S j) (lm_es m)) -> In b (aentry_blks y) ->
      In b (dcB_T cx m j si rest0)).
  { intros y b Hy Hb. unfold dcB_T. apply in_or_app. left. unfold dcB_CA.
    apply in_concat. exists (aentry_blks y). split; [apply in_map; exact Hy | exact Hb]. }
  (* ---- the bytes drain keeps ---- *)
  assert (KBLK : forall p n a, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n ->
      ~ inFP (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m)) a ->
      abyte_kept W mem W2 mem2 a).
  { intros p n a H1 H2 Ha Hnf.
    pose proof (blk_img segs B LAWS ly S W mem md p n a HAR H1 Ha) as Hni.
    destruct (dr_blk ly S W mem md p n HAR H1) as (Hp1 & Hp2 & _).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; left. exists p, n. split; [exact H1|]. split; [exact H2|]. split; [exact Ha | exact Hnf]. }
  assert (KT : forall b a, In b (dcB_T cx m j si rest0) -> fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem2 a).
  { intros [p n] a HbT Ha. cbn [fst snd] in Ha.
    destruct (dcB_in_rest _ _ _ _ HNDS HP1' (KTR _ HbT)) as (HnX & HbL).
    pose proof (dcB_T_ne _ _ _ _ _ _ HNDS HP1' HRT HbT) as Hng.
    destruct (dr_blk ly S W mem md p n HAR HbL) as (_ & _ & Hn0).
    apply (KBLK p n a HbL (KTL2 _ (KTR _ HbT)) ltac:(lia)).
    exact (dcB_nfp_blk ly S W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ p n a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL HbL HnX ltac:(lia) (or_introl Hng)). }
  assert (KTAB : forall a, lm_G m <= a < lm_G m + ATABLE ->
      ~ (lm_G m + AENT * Z.of_nat j <= a < lm_G m + AENT * Z.of_nat j + AENT) -> abyte_kept W mem W2 mem2 a).
  { intros a Ha Hn.
    destruct (dcB_in_rest _ _ _ _ HNDS HP1' HGr) as (HnX & HbL).
    apply (KBLK (lm_G m) ATABLE a HbL (KTL2 _ HGr) ltac:(replace (req_size ATABLE) with ATABLE by reflexivity; lia)).
    exact (dcB_nfp_blk ly S W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ (lm_G m) ATABLE a HAR HGin (proj1 HSA)
             (proj2 HSA) HXL HbL HnX ltac:(replace (req_size ATABLE) with ATABLE by reflexivity; lia) (or_intror Hn)). }
  assert (KSTK : forall a, lf_F cx <= a < sp0 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (Hsegs a Hi); lia).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    left. split; [lia | lia]. }
  assert (FFb : 4096 <= FF /\ FF + 128 <= alloc_ceiling).
  { destruct (frames_bounds segs B LAWS ly S W mem md 1 fpos HAR Hfin) as (Hf0 & Hfc & _).
    rewrite HFFe in Hf0, Hfc. replace (fs_frame_bytes 1) with 128 in Hfc by reflexivity. lia. }
  assert (KFF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (Hfr : frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + fs_frame_bytes 1)
      by (rewrite HFFe; replace (fs_frame_bytes 1) with 128 by reflexivity; exact Ha).
    pose proof (frm_img segs B LAWS ly S W mem md 1 fpos a HAR Hfin Hfr) as Hni.
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; right; right. exists 1, fpos. split; [exact Hfin|].
    split; [left; unfold in_zr, frame_rng; cbn [fst snd]; exact Hfr|].
    exact (dcB_nfp_frm ly S W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ 1 fpos a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL Hfin (or_introl Hfr)). }
  assert (KSH : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (FF8 : 0 <= FF / 8 /\ 8 * (FF / 8) <= FF) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    unfold SB in Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (Hsegs a Hi); lia).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; right; right. exists 1, fpos. split; [exact Hfin|].
    assert (Hsh : shadow_addr (frame_addr ly 1 fpos) <= a < shadow_addr (frame_addr ly 1 fpos) + fs_frame_bytes 1 / 8).
    { rewrite HFFe. replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr, SHADOW_OFF. lia. }
    split; [right; unfold in_zr; cbn [fst snd]; exact Hsh|].
    exact (dcB_nfp_frm ly S W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ 1 fpos a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL Hfin (or_intror Hsh)). }
  assert (HFPpos : Forall (fun r => 0 < fst r)
      (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m))).
  { unfold dr_fp. constructor; [cbn [fst]; lia|]. apply Forall_forall. intros r Hr. unfold ablocks_fp in Hr.
    apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst].
    destruct (dr_blk ly S W mem md p n HAR (HXL _ Hb)) as (Hp & _).
    lia. }
  assert (KIMG : forall a, inG DR_GK a \/ rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. destruct (dcB_GK_out a Ha) as (HnD & Hne).
    assert (HGa : inG G_fr a) by (destruct Ha as [Ha | Ha]; [exact (HG_GK a Ha) | exact (HGlock a Ha)]).
    destruct (HG a HGa) as (Hi & Hno & _). pose proof (Hsegs a Hi) as Hlo.
    apply dj_bk; [lia | intros _; exact HGa |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | exact HnD |].
    right; right; right; left. split; [exact Hi|]. split; [exact Hno|]. split; [exact Hne|].
    apply fp_spares_closed. apply sink_closed_pos. exact HFPpos. }
  (* ---- the context after the call ---- *)
  destruct (dcF_frame_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos HJD) as (Efr & Efl).
  assert (HFF2 : frame_addr ly2 1 fpos = FF) by (rewrite Efr; exact HFFe).
  assert (WF2 : forall a, lf_F cx <= a < sp0 -> writable_at segs (arm W2 mem2) a).
  { intros a Ha. apply (apresent_writable segs).
    exact (dcF_pres cx fpos ly2 S2 W2 mem2 md2 (k + k1) HJ2 a ltac:(unfold LLVMF_STK; lia)). }
  assert (HFR2 : aframe_at cx FF W2 mem2)
    by (apply (dc_aframe_kept cx FF W W2 mem mem2 HFR ltac:(lia) ltac:(intros a Ha _; apply KSTK; lia) WF2 KFF KSH)).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly 1 fpos))
    by (apply (dr_sv8_kept W W2 mem mem2); [intros x Hx; apply KFF; lia | exact HFL]).
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { destruct HIN as (Hn & Hpl).
    assert (HbT : 0 < c_n cx -> In (c_p cx, c_n cx) (dcB_T cx m j si rest0)).
    { intros Hn1. unfold dcB_T. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold input_blks. rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    split.
    - destruct Hn as [Hn | (Hn1 & Hin)]; [left; exact Hn | right; split; [exact Hn1|]].
      exact (KTL2 _ (KTR _ (HbT (proj1 Hn1)))).
    - apply (akept_garr8 W mem); [|exact Hpl]. intros x Hx. rewrite length_map, Hnlen in Hx.
      destruct Hn as [(Hn0 & _) | (Hn1 & _)]; [lia|].
      exact (KT (c_p cx, c_n cx) x (HbT (proj1 Hn1)) ltac:(cbn [fst snd]; lia)). }
  assert (HRV2 : rom_view segs W2 mem2)
    by exact (ajournal_gx_rom_view segs B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD dcB_rom_out HRV).
  pose proof (dt_jt_kept W W2 mem mem2 HRV HRV2 HJT) as HJT2.
  assert (SVN2 : sv8 W2 mem2 (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact SVN]. intros x Hx. apply KSTK. unfold DR_N in Hx. lia. }
  assert (S1922 : sv8 W2 mem2 (lf_F cx + DR_AT) 0).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact S192]. intros x Hx. apply KSTK. unfold DR_AT in Hx. lia. }
  (* ---- the model after the call ---- *)
  assert (HLEN1 : Z.of_nat (length (dr_O1 m h LB)) =
      (if dr_live (lm_c m) h then Z.of_nat (length (lm_O m)) + dr_tot h else Z.of_nat (length (lm_O m)))).
  { unfold dr_O1. destruct (dr_live (lm_c m) h); [|reflexivity].
    rewrite length_app, Nat2Z.inj_add, (dc_LB_len LB _ D38). reflexivity. }
  assert (HO1 : aout_at B fr_RG ly2 S2 W2 mem2 (dc_ctl (dr_ctl (lm_c m) h ev') ev') (dr_O1 m h LB) (lm_mx m)
                  (Z.of_nat (length (dr_O1 m h LB))) (dr_cap1 m j h) out').
  { rewrite HLEN1. unfold dr_O1, dr_cap1. exact HOUT2. }
  assert (HREL2 : arelay_at B fr_RG ly2 S2 W2 mem2 (lm_G m) (set_nth j e' (lm_es m))).
  { pose proof HN3 as (_ & _ & Hq1 & Hq2 & _).
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL1]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL2]|].
    split; [rewrite set_nth_length; apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL3]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL4]|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL5]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL6]|].
    split; [rewrite set_nth_length; exact RL7|].
    split; [exact (KTL2 _ HGr)|].
    split.
    { exists tl. apply (dr_tbl_upd W W2 mem mem2 (lm_G m) (lm_es m) tl j e' HTAB HPAD Hq1 Hq2 Hj HN1).
      intros a Ha Hn. exact (proj1 (KTAB a Ha Hn)). }
    split.
    { apply Forall_forall. intros y Hy.
      destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy']; [exact HN3|].
      assert (HyE : In y (lm_es m)) by exact (dr_in_rm rentry j y (lm_es m) Hy').
      rewrite Forall_forall in HENT, HKY.
      apply (aentry_ok_kept B ly S W mem ly2 S2 W2 mem2 y (HENT y HyE)).
      - intros r Hr x Hx.
        destruct (dj_aentry_fp ly S W mem y (HENT y HyE) (HKY y HyE) r Hr x Hx) as [[] | (b & Hb & Hbx)].
        exact (KT b x (HCAin y b Hy' Hb) Hbx).
      - intros b Hb. exact (KTL2 b (KTR b (HCAin y b Hy' Hb))). }
    split.
    { rewrite dr_map_set_nth, D9.
      assert (Hfe : re_fd (nth j (lm_es m) dr_e0) = nth j (map re_fd (lm_es m)) (re_fd dr_e0))
        by (rewrite map_nth; reflexivity).
      rewrite Hfe, dcB_set_nth_nth. exact HNDF. }
    (* arelay_at's last conjunct (lib/B/W_rep.v:166-171, cand11): no entry's block is the table's.  The drained entry
       e''s blocks and the table both sit in drain's post permutation, the table in `rest` (HGr), and the live
       blocks are duplicate-free; every other entry keeps the old conjunct. *)
    apply Forall_forall. intros y Hy b Hb Heq.
    destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy'].
    - pose proof (Permutation_NoDup HP2 HNDS2) as HNDR.
      apply (dc_nd_app _ _ b HNDR Hb). rewrite Heq.
      apply in_or_app; right; apply in_or_app; right; exact HGr.
    - rewrite Forall_forall in HETB. exact (HETB y (dr_in_rm rentry j y (lm_es m) Hy') b Hb Heq). }
  assert (HNE2 : amodel_ne ly2 S2 W2 mem2 (dr_m1 m j si h h' e' ev' LB out') true).
  { unfold dr_m1, dr_step, amodel_ne. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [rewrite set_nth_length; exact Hlen4|].
    split.
    { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
      - rewrite set_nth_same by lia. exact HSRC.
      - rewrite set_nth_other by lia.
        pose proof (HSL i Hi) as Hs. revert Hs.
        destruct (nth i (lm_hs m) None) as [hi|] eqn:Ehi; intros Hs; cbn [aslot] in Hs |- *.
        + apply (asrc_at_kept B ly S W mem ly2 S2 W2 mem2 _ hi Hs).
          * intros r Hr x Hx. destruct (dj_asrc_fp ly S W mem _ hi Hs r Hr x Hx) as [Hin | (b & Hb & Hbx)].
            -- cbv beta in Hin. apply HGS; unfold ASRC in *; lia.
            -- exact (KT b x (HCSin i hi b Hi Hne Ehi Hb) Hbx).
          * intros b Hb. exact (KTL2 b (KTR b (HCSin i hi b Hi Hne Ehi Hb))).
        + destruct Hs as (Hz & Hw). split.
          * apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx.
            rewrite Z2Nat.id in Hx by (unfold ASRC; lia). apply HGS; unfold ASRC in *; lia.
          * apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply HGS; unfold ASRC in *; lia. }
    split; [exact HREL2|].
    split; [exists ev'; exact HO1|].
    split; [apply (agone_at_kept fr_RG W mem W2 mem2 (lm_gn m) HGONE); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; dcB_gk Hx|].
    split; [apply (alock_at_kept fr_RG W mem W2 mem2 true HLOCK); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; right; exact Hx|].
    split; [apply (awake_at_kept fr_RG W mem W2 mem2 HWAKE); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; dcB_gk Hx|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HNFD]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HNFDW]|].
    split; [exact HNFDr|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HTUP]|].
    split; [destruct HLST as (lst & Hl); exists lst; apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact Hl]|].
    apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HLSTW]. }
  assert (HPm1 : Permutation (ablocks B ly2 S2)
      (input_blks cx ++ model_blks (dr_m1 m j si h h' e' ev' LB out') ++ rest0)).
  { unfold dr_m1, dr_step, model_blks. cbn [lm_G lm_es lm_hs lm_cap lm_out]. unfold dr_cap1.
    apply (dcB_perm_post _ _ _ _ _ _ _ _ (dcB_CA (lm_es m) j) (dcB_CS (lm_hs m) si) rest _ HP2 HRT).
    - exact (dr_concat_set_nth_perm _ _ aentry_blks (lm_es m) j e' Hj).
    - pose proof (dr_concat_set_nth_perm _ _ slot_blks (lm_hs m) si (Some h') ltac:(lia)) as Hq.
      cbn [slot_blks] in Hq. exact Hq. }
  assert (HSEP1 : ablocks_sep B fr_FP cx (dr_m1 m j si h h' e' ev' LB out') ly2 S2).
  { split; [exists rest0; exact HPm1|].
    intros b Hb.
    assert (HbL2 : In b (ablocks B ly2 S2)).
    { apply (Permutation_in _ (Permutation_sym HPm1)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
    destruct (in_dec dc_dec b (ablocks B ly S)) as [HbS | HbS].
    - apply HSEP2.
      apply (Permutation_in _ HP1') in HbS. apply in_app_or in HbS as [HbX | HbR]; [exact (HXM b HbX)|].
      apply (Permutation_in _ HRT) in HbR. destruct HbR as [<- | HbT]; [unfold model_blks; left; reflexivity|].
      unfold dcB_T in HbT. apply in_app_or in HbT as [HbA | HbT].
      + unfold model_blks. right. apply in_or_app. left.
        apply (Permutation_in _ (Permutation_sym HCA)). apply in_or_app. right. exact HbA.
      + apply in_app_or in HbT as [HbC | HbT].
        * unfold model_blks. right. apply in_or_app. right. apply in_or_app. left.
          apply (Permutation_in _ (Permutation_sym HCS)). apply in_or_app. right. exact HbC.
        * exfalso. pose proof (Permutation_NoDup HPm1 HNDS2) as Hnd.
          apply in_app_or in HbT as [HbI | HbR0].
          -- exact (dc_nd_app _ _ b Hnd HbI (in_or_app _ _ _ (or_introl Hb))).
          -- apply (dc_nd_app (input_blks cx ++ model_blks (dr_m1 m j si h h' e' ev' LB out')) rest0 b);
               [rewrite <- app_assoc; exact Hnd | apply in_or_app; right; exact Hb | exact HbR0].
    - destruct (in_dec dc_dec b (ablocks B (c_ly cx) (c_S cx))) as [HbE | HbE]; [right | left; exact HbE].
      intros a Ha. destruct b as [p n]. cbn [fst snd] in Ha.
      replace a with (p + (a - p)) by lia. apply (HGONE0 p n (a - p) HbE HbS). lia. }
  assert (HKY1 : Forall (fun e0 => Z.of_nat (length (re_keys e0)) <= re_nheld e0)
      (lm_es (dr_m1 m j si h h' e' ev' LB out'))).
  { unfold dr_m1, dr_step. cbn [lm_es]. apply Forall_forall. intros y Hy.
    destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy']; [exact HKE|].
    rewrite Forall_forall in HKY. exact (HKY y (dr_in_rm rentry j y (lm_es m) Hy')). }
  (* ---- the state at 0x8490c ---- *)
  exists ly2, S2, e', h', out', ev', LB.
  split; [|split].
  - exists regs2, mem2, md2, (k + k1). split; [reflexivity|].
    split.
    { assert (P23 : getr regs2 23 = w64 (rg_lock fr_RG))
        by (rewrite (dj_pres (ms_regs ms) regs2 23%bv HPR ltac:(dj_cs)); exact Q23d).
      exact (dcF_regs_kept cx t m j si FF (rg_lock fr_RG) (rg_lock fr_RG) regs regs2
               (fun r Hr => eq_trans (dcF_pres_K (ms_regs ms) regs2 HPR r Hr) (KR3 r Hr)) P23 HR). }
    split; [exact HJ2|]. split; [exact HFF2|].
    split; [rewrite Efl; exact (conj HFR2 (conj HFL2 (conj HIN2 (conj HRV2 (conj HJT2 SVN2)))))|].
    split; [exact S1922|].
    split; [exact HNE2|]. split; [exact HSEP1 | exact HKY1].
  - exact HMO.
  - unfold dr_dfun. cbv zeta.
    split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|]. split; [exact D13|].
    split; [exact D14|]. split; [exact D15|]. split; [exact D16|]. split; [exact D18|]. split; [exact D19|].
    split; [exact D24|]. split; [exact D25|]. split; [exact D26|]. split; [exact D27|]. split; [exact D28|].
    split; [exact D32|]. split; [exact D33|]. split; [exact D35|]. split; [exact D36|]. split; [exact D37|].
    split; [exact D38 | exact D22].
Qed.

(* ---------------- stage E's kit (dcE_) ---------------- *)
(* a block address of a source is one of its blocks' *)
Lemma dcE_hs_blocks : forall h x, In x (hs_blocks h) -> exists n, In (x, n) (asrc_blks h).
Proof.
  intros h x Hx. unfold hs_blocks, list_blocks in Hx. unfold asrc_blks, alist_blks.
  repeat rewrite in_app_iff in Hx.
  destruct Hx as [[Hx | Hx] | [[<- | []] | [[Hx | Hx] | [Hx | Hx]]]].
  - destruct (hl_cap (hs_pending h) =? 0); [destruct Hx|]. destruct Hx as [<- | []].
    eexists. right. apply in_or_app. left. apply in_or_app. left. left. reflexivity.
  - apply in_map_iff in Hx as (r & <- & Hr). eexists. right. apply in_or_app. left. apply in_or_app. right.
    apply in_map_iff. exists r. split; [reflexivity | exact Hr].
  - eexists. left. reflexivity.
  - destruct (hl_cap (hs_expected h) =? 0); [destruct Hx|]. destruct Hx as [<- | []].
    eexists. right. apply in_or_app. right. apply in_or_app. left. apply in_or_app. left. left. reflexivity.
  - apply in_map_iff in Hx as (r & <- & Hr). eexists. right. apply in_or_app. right. apply in_or_app. left.
    apply in_or_app. right. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
  - destruct (hl_cap (hs_held h) =? 0); [destruct Hx|]. destruct Hx as [<- | []].
    eexists. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity.
  - apply in_map_iff in Hx as (r & <- & Hr). eexists. right. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. right. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
Qed.
(* the stream's bytes, read out of the out block's garr8 *)
Lemma dcE_ob_at : forall (W : world segs) mem out (O junk : list byte),
  garr8 segs (arm W mem) out (bzs (O ++ junk)) -> ob_at W mem out O.
Proof.
  intros W mem out O junk Hg i Hi.
  assert (Hj : (Z.to_nat i < length (bzs (O ++ junk)))%nat) by (unfold bzs; rewrite length_map, length_app; lia).
  destruct (Hg _ Hj) as [Hv Hr]. unfold arm in Hv.
  pose proof (dj_av1 W mem _ 1%nat _ Hv ltac:(lia)) as Ha. rewrite Z2Nat.id in Ha by lia.
  rewrite Ha. f_equal. rewrite nth_bzs, app_nth1 by lia.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) O (Z_to_bv 8 0))) as Hb. change (bv_modulus 8) with 256 in Hb.
  apply dc_lb1. exact Hb.
Qed.
(* a read-only literal, as the ASan view reads it *)
Lemma dcE_in_rom_b : forall a,
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
    (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs = true -> in_rom segs a.
Proof.
  intros a H. apply existsb_exists in H as (sg & Hs & Hb). apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply Bool.negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists sg. split; [exact Hs|]. split; [exact H0 | lia].
Qed.
Definition dcE_litb (base : Z) (l : list Z) : bool :=
  forallb (fun j => existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? base + Z.of_nat j) &&
    (base + Z.of_nat j <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs &&
    match seg_rom segs (Z_to_bv 64 (base + Z.of_nat j)) with Some b => bv_unsigned b =? nth j l 0 | None => false end)
  (seq 0 (length l)).
Lemma dcE_lit : forall (W : world segs) mem base l,
  rom_view segs W mem -> dcE_litb base l = true -> garr8 segs (arm W mem) base l.
Proof.
  intros W mem base l HR Hb j Hj. unfold dcE_litb in Hb. rewrite forallb_forall in Hb.
  specialize (Hb j ltac:(apply in_seq; lia)). apply andb_prop in Hb as [Hrb Hv].
  pose proof (dcE_in_rom_b _ Hrb) as Hrom. pose proof (HR _ Hrom) as Ha.
  destruct (seg_rom segs (Z_to_bv 64 (base + Z.of_nat j))) as [b|] eqn:Eb; [|discriminate].
  apply Z.eqb_eq in Hv. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|lia].
  intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r. unfold arm.
  unfold aview in Ha. cbn [option_map] in Ha.
  destruct (mbyte segs (mrestrict (w_H W) mem) (base + Z.of_nat j)) as [b'|] eqn:Eb'; [|discriminate].
  injection Ha as Ha. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Ha, Hv.
  rewrite dc_lb1 by lia. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.
Lemma dcE_lits : dcE_litb (VAL A_lit_gesture) RelayModel.K_GESTURE = true /\
  dcE_litb (VAL A_lit_begin) RelayModel.W_BEGIN = true /\ dcE_litb (VAL A_lit_end) RelayModel.W_END = true.
Proof. vm_compute. repeat split. Qed.
Lemma dcE_vals : VAL A_g_nout = rg_nout fr_RG /\ VAL A_g_out = rg_out fr_RG /\ VAL A_g_gone = rg_gone fr_RG /\
  VAL A_g_s = rg_s fr_RG.
Proof. vm_compute. repeat split. Qed.
Lemma dcE_cnl_stk : CNL_STK = 16640.
Proof. reflexivity. Qed.
(* what a callee's journal (empty own) keeps, as abyte_kept *)
Lemma dcE_kept : forall Gc XO OUT STK sp FP ly S (W : world segs) mem md ly' S' (W' : world segs) mem' md' kk a,
  gx_ok segs B Gc ->
  ajournal_gx segs B Gc XO OUT STK sp FP ly S W mem md [] ly' S' W' mem' md' kk ->
  0 <= a < 2 ^ 64 -> ~ inG Gc a -> (in_img segs a -> inG G_fr a) ->
  ((alloc_ceiling <= a /\ ~ (sp - STK <= a < sp + XO)) \/
   (sp <= a < sp + XO /\ ~ inFP OUT a) \/
   (exists p n, In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n /\
      ~ inFP FP a) \/
   (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
      fp_spares FP a) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) /\
      ~ inFP FP a)) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros Gc XO OUT STK sp FP ly S W mem md ly' S' W' mem' md' kk a HGx HJX Ha HnG Hig Hc.
  apply (dj_bk W W' mem mem' a Ha Hig).
  exact (dj_keep Gc XO OUT STK sp FP ly S W mem md [] ly' S' W' mem' md' kk a HGx HJX Ha HnG Hc).
Qed.
Lemma dcE_fp_closed : forall ly S (W : world segs) mem md L,
  AR segs B ly S W mem md -> (forall b, In b L -> In b (ablocks B ly S)) -> ~ YI16.sink_open_fp (blk_FP L).
Proof.
  intros ly S W mem md L HAR HL (r & Hr & H0). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HL _ Hb)) as (_ & H4 & _). cbn [fst snd] in H0. lia.
Qed.
Lemma dcE_notFP : forall ly S (W : world segs) mem md L p n a,
  AR segs B ly S W mem md -> (forall b, In b L -> In b (ablocks B ly S)) -> In (p, n) (ablocks B ly S) ->
  ~ In (p, n) L -> p <= a < p + req_size n -> ~ inFP (blk_FP L) a.
Proof.
  intros ly S W mem md L p n a HAR HL Hpn Hnot Ha (r & Hr & Hra). unfold blk_FP in Hr.
  apply in_map_iff in Hr as ([q m] & <- & Hb). cbn [fst snd] in Hra.
  apply (dj_apart ly S W mem md p n q m a HAR Hpn (HL _ Hb)); [| exact Ha | exact Hra].
  intros E. apply Hnot. rewrite E. exact Hb.
Qed.
Section dcE_keep.
Variables (Gc : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp : Z) (L : list (Z * Z)).
Variables (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model).
Variables (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (kk : Z).
Hypothesis KGx : gx_ok segs B Gc.
Hypothesis KJ : ajournal_gx segs B Gc XO OUT STK sp (blk_FP L) ly S W mem md [] ly' S' W' mem' md' kk.
Hypothesis KAR : AR segs B ly S W mem md.
Hypothesis KL : forall b, In b L -> In b (ablocks B ly S).
Lemma dcE_nG_img : forall a, inG Gc a -> in_img segs a.
Proof. intros a Ha. exact (proj1 (KGx a Ha)). Qed.
Lemma dcE_kept_blk : forall p n a,
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> ~ In (p, n) L -> p <= a < p + req_size n ->
  abyte_kept W mem W' mem' a.
Proof.
  intros p n a H1 H2 Hnot Ha.
  destruct (al_blocks _ _ LAWS ly S W mem md p n KAR H1) as (_ & H4 & Hc & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hni : ~ in_img segs a) by exact (blk_img segs B LAWS ly S W mem md p n a KAR H1 Ha).
  apply (dcE_kept Gc XO OUT STK sp (blk_FP L) ly S W mem md ly' S' W' mem' md' kk a KGx KJ);
    [lia | intros HGa; exact (Hni (dcE_nG_img a HGa)) | intros Hi; exact (False_ind _ (Hni Hi)) |].
  right; right; left. exists p, n. repeat split; try assumption; try lia.
  exact (dcE_notFP ly S W mem md L p n a KAR KL H1 Hnot Ha).
Qed.
Lemma dcE_kept_img : forall a, inG G_fr a -> ~ inG Gc a -> ~ (as_errno B <= a < as_errno B + 4) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros a HGa HnG He. destruct (HG a HGa) as (Hi & Hno & _).
  pose proof (pa_segs_low a Hi) as Hlo. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (dcE_kept Gc XO OUT STK sp (blk_FP L) ly S W mem md ly' S' W' mem' md' kk a KGx KJ);
    [lia | exact HnG | intros _; exact HGa |].
  right; right; right; left. split; [exact Hi|]. split; [exact Hno|]. split; [exact He|].
  apply fp_spares_closed. exact (dcE_fp_closed ly S W mem md L KAR KL).
Qed.
Lemma dcE_kept_frame : forall cid pos a, In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros cid pos a Hfr Hr.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds segs B LAWS ly S W mem md cid pos KAR Hfr) as (Hf0 & Hfc & Hfh).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)) as SB1.
  pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)) as SB2.
  pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as SB3.
  assert (Hni : ~ in_img segs a).
  { intros Hi. destruct Hr as [Hr | Hr].
    - exact (frm_img segs B LAWS ly S W mem md cid pos a KAR Hfr Hr Hi).
    - pose proof (pa_segs_low a Hi). unfold in_zr in Hr. cbn [fst snd] in Hr. zlia. }
  apply (dcE_kept Gc XO OUT STK sp (blk_FP L) ly S W mem md ly' S' W' mem' md' kk a KGx KJ);
    [ unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr; destruct Hr as [Hr | Hr]; zlia
    | intros HGa; exact (Hni (dcE_nG_img a HGa)) | intros Hi; exact (False_ind _ (Hni Hi)) |].
  right; right; right; right. exists cid, pos. split; [exact Hfr|]. split; [exact Hr|].
  intros (r & Hrin & Hra). unfold blk_FP in Hrin. apply in_map_iff in Hrin as ([b m] & <- & Hb). cbn [fst snd] in Hra.
  pose proof (KL _ Hb) as Hbin.
  destruct (al_blocks _ _ LAWS ly S W mem md b m KAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
  pose proof (sep_block_frame segs B LAWS ly S W mem md b m cid pos KAR Hbin Hfr) as Hd.
  unfold zdisjoint, frame_rng, in_zr in Hd, Hr. cbn [fst snd] in Hd, Hr.
  destruct Hr as [Hr|Hr]; zlia.
Qed.
End dcE_keep.
(* the controller's stream across a callee that keeps every byte of it but errno, which it re-reads *)
Definition dcE_ofp (cap out : Z) : list (Z * Z) :=
  [(rg_send_max fr_RG, rg_send_max fr_RG + 8); (rg_nout fr_RG, rg_nout fr_RG + 8);
   (rg_capout fr_RG, rg_capout fr_RG + 8); (rg_out fr_RG, rg_out fr_RG + 8); (rg_client fr_RG, rg_client fr_RG + 4);
   (rg_client_broken fr_RG, rg_client_broken fr_RG + 1); (rg_send_dead fr_RG, rg_send_dead fr_RG + 1);
   (rg_send_eintr fr_RG, rg_send_eintr fr_RG + 1)] ++ (if cap =? 0 then [] else [(out, out + cap)]).
Lemma dcE_aout : forall ly S (W : world segs) mem ly' S' (W' : world segs) mem' c O mx no cap out v,
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  akept W mem W' mem' (dcE_ofp cap out) ->
  (forall b, In b (aout_blks cap out) -> In b (ablocks B ly' S')) ->
  val_mem segs (arm W' mem') (as_errno B) 4 v -> awr W' mem' (as_errno B) 4 -> 0 <= v < 2 ^ 32 ->
  aout_at B fr_RG ly' S' W' mem' (dc_ctl c v) O mx no cap out.
Proof.
  intros ly S W mem ly' S' W' mem' c O mx no cap out v
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HB Hv Hw Hvr.
  assert (KC : forall a n, In (a, a + n) (dcE_ofp cap out) -> forall x, a <= x < a + n -> abyte_kept W mem W' mem' x)
    by (intros a n Hin x Hx; exact (HK (a, a + n) Hin x Hx)).
  cbn [dc_ctl ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_max fr_RG) 8); [unfold dcE_ofp; dt_infp | lia] | exact H1]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_max fr_RG) 8); unfold dcE_ofp; dt_infp | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_nout fr_RG) 8); [unfold dcE_ofp; dt_infp | lia] | exact H3]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_nout fr_RG) 8); unfold dcE_ofp; dt_infp | exact H4]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_capout fr_RG) 8); [unfold dcE_ofp; dt_infp | lia] | exact H5]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_capout fr_RG) 8); unfold dcE_ofp; dt_infp | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_out fr_RG) 8); [unfold dcE_ofp; dt_infp | lia] | exact H7]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_out fr_RG) 8); unfold dcE_ofp; dt_infp | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_client fr_RG) 4); [unfold dcE_ofp; dt_infp | lia] | exact H9]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_client fr_RG) 4); unfold dcE_ofp; dt_infp | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_client_broken fr_RG) 1); [unfold dcE_ofp; dt_infp | lia] | exact H11]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_client_broken fr_RG) 1); unfold dcE_ofp; dt_infp | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_dead fr_RG) 1); [unfold dcE_ofp; dt_infp | lia] | exact H13]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_dead fr_RG) 1); unfold dcE_ofp; dt_infp | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_eintr fr_RG) 1); [unfold dcE_ofp; dt_infp | lia] | exact H15]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_eintr fr_RG) 1); unfold dcE_ofp; dt_infp | exact H16]|].
  split; [exact Hv|]. split; [exact Hw|]. split; [exact Hvr|].
  do 6 (split; [assumption|]).
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|]. split; [exact Hno|].
  split; [apply HB; unfold aout_blks; rewrite Ec; left; reflexivity|].
  exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  apply (KC out cap); [unfold dcE_ofp; rewrite Ec; dt_infp | lia].
Qed.
(* the model after check_no_loss: slot si is the callee's, every other byte the model reads is kept *)
Lemma dcE_model_kept : forall ly S (W : world segs) mem ly2 S2 (W2 : world segs) mem2 md2 mc si h' R HA,
  AR segs B ly2 S2 W2 mem2 md2 -> (si < 4)%nat -> HA = rg_s fr_RG + ASRC * Z.of_nat si ->
  amodel_ne ly S W mem mc false ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es mc) ->
  asrc_at B ly2 S2 W2 mem2 HA h' ->
  (forall i b, (i < 4)%nat -> i <> si -> In b (slot_blks (nth i (lm_hs mc) None)) -> In b R) ->
  (forall b, In b (arelay_blks (lm_G mc) (lm_es mc)) -> In b R) ->
  (forall b, In b (aout_blks (lm_cap mc) (lm_out mc)) -> In b R) ->
  (forall b, In b R -> In b (ablocks B ly2 S2)) ->
  (forall b a, In b R -> fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem2 a) ->
  (forall a, inG G_fr a -> ~ inG [(HA + 64, 32)] a -> ~ (as_errno B <= a < as_errno B + 4) ->
     abyte_kept W mem W2 mem2 a) ->
  amodel_ne ly2 S2 W2 mem2 (dc_setsrc mc si h') false.
Proof.
  intros ly S W mem ly2 S2 W2 mem2 md2 mc si h' R HA AR2 Hsi EHA HMOD HKY HSRC2 HOi HGER HAOR Rin2 KBLK KI0.
  assert (EASRC : ASRC = 96) by reflexivity.
  pose proof HMOD as (Hlen4 & HSL & HREL & (ev & HOUT) & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  assert (KGL : forall a, inG G_fr a -> (a < rg_s fr_RG \/ rg_s fr_RG + 4 * ASRC <= a) -> a < rg_out fr_RG + 8 ->
      abyte_kept W mem W2 mem2 a).
  { intros a HGa Hs He. apply KI0; [exact HGa | rewrite dcE_inG1; dt_num | dt_num]. }
  assert (KGS : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> ~ (HA + 64 <= a < HA + 96) ->
      abyte_kept W mem W2 mem2 a).
  { intros a Ha Hn. apply KI0; [apply HGs; exact Ha | rewrite dcE_inG1; lia | dt_num]. }
  assert (KDG : forall x n a, In (x, n) DR_GK -> x <= a < x + n -> abyte_kept W mem W2 mem2 a).
  { intros x n a Hx Ha. apply KGL; [apply HG_GK; exact (dcE_inG_mem _ x n a Hx Ha) | |];
      unfold DR_GK in Hx; cbn [In] in Hx;
      repeat (destruct Hx as [Hx | Hx]; [injection Hx as <- <-; dt_num|]);
      destruct Hx. }
  assert (KSL : forall x n a, In (x, n) [(rg_client_broken fr_RG, 1); (rg_send_eintr fr_RG, 1); (rg_nout fr_RG, 8);
      (rg_capout fr_RG, 8); (rg_out fr_RG, 8)] -> x <= a < x + n -> abyte_kept W mem W2 mem2 a).
  { intros x n a Hx Ha. apply KGL.
    - apply HG_DR. apply (dcE_inG_mem _ x n a); [|exact Ha]. unfold G_DR, G_SL. right. cbn [In] in Hx |- *. tauto.
    - cbn [In] in Hx. repeat (destruct Hx as [Hx | Hx]; [injection Hx as <- <-; dt_num|]). destruct Hx.
    - cbn [In] in Hx. repeat (destruct Hx as [Hx | Hx]; [injection Hx as <- <-; dt_num|]). destruct Hx. }
  assert (HSL2 : forall i, (i < 4)%nat -> aslot B ly2 S2 W2 mem2 i (nth i (set_nth si (Some h') (lm_hs mc)) None)).
  { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
    - rewrite set_nth_same by lia. cbn [aslot]. rewrite <- EHA. exact HSRC2.
    - rewrite set_nth_other by lia.
      pose proof (HOi i) as HOi'. pose proof (HSL i Hi) as Hs.
      destruct (nth i (lm_hs mc) None) as [hi|] eqn:Ehi; rewrite ?Ehi in Hs, HOi'; cbn [aslot slot_blks] in Hs, HOi' |- *.
      + apply (asrc_at_kept B ly S W mem ly2 S2 W2 mem2 _ hi Hs).
        * intros r Hr a Ha. destruct (dj_asrc_fp ly S W mem _ hi Hs r Hr a Ha) as [Hin | (b & Hb & Hab)].
          -- cbv beta in Hin. rewrite EASRC in Hin. apply KGS; [dt_num | rewrite EHA; dt_num].
          -- exact (KBLK b a (HOi' b Hi Hne Hb) Hab).
        * intros b Hb. exact (Rin2 _ (HOi' b Hi Hne Hb)).
      + destruct Hs as [G1 G2]. split.
        * apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx. rewrite EASRC in Hx.
          apply KGS; [dt_num | rewrite EHA; dt_num].
        * apply (akept_awr W mem); [|exact G2]. intros x Hx. rewrite EASRC in Hx.
          apply KGS; [dt_num | rewrite EHA; dt_num]. }
  assert (HREL2 : arelay_at B fr_RG ly2 S2 W2 mem2 (lm_G mc) (lm_es mc)).
  { apply (arelay_at_kept B fr_RG ly S W mem ly2 S2 W2 mem2 _ _ HREL).
    - intros r Hr a Ha. destruct (dj_arelay_fp ly S W mem _ _ HREL HKY r Hr a Ha) as [Hg | (b & Hb & Hab)].
      + destruct Hg as [Hg | [Hg | Hg]].
        * apply (KDG (rg_src fr_RG) 8 a); [dt_infp | exact Hg].
        * apply (KDG (rg_nsrc fr_RG) 4 a); [dt_infp | exact Hg].
        * apply (KDG (rg_capsrc fr_RG) 4 a); [dt_infp | exact Hg].
      + exact (KBLK b a (HGER b Hb) Hab).
    - intros b Hb. exact (Rin2 _ (HGER b Hb)). }
  destruct (ERR ly2 S2 W2 mem2 md2 AR2) as ((ev2 & Mev2 & Hev2) & Wev2).
  assert (HOUT2 : aout_at B fr_RG ly2 S2 W2 mem2 (dc_ctl (lm_c mc) ev2) (lm_O mc) (lm_mx mc)
                    (Z.of_nat (length (lm_O mc))) (lm_cap mc) (lm_out mc)).
  { apply (dcE_aout ly S W mem ly2 S2 W2 mem2 _ _ _ _ _ _ ev2 HOUT);
      [| intros b Hb; exact (Rin2 _ (HAOR b Hb)) | exact Mev2 | exact Wev2 | exact Hev2].
    intros r Hr a Ha. unfold dcE_ofp in Hr. apply in_app_or in Hr as [Hr | Hr].
    - cbn [In] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]; cbn [fst snd] in Ha.
      + apply (KDG (rg_send_max fr_RG) 8 a); [dt_infp | lia].
      + apply (KSL (rg_nout fr_RG) 8 a); [dt_infp | lia].
      + apply (KSL (rg_capout fr_RG) 8 a); [dt_infp | lia].
      + apply (KSL (rg_out fr_RG) 8 a); [dt_infp | lia].
      + apply (KDG (rg_client fr_RG) 4 a); [dt_infp | lia].
      + apply (KSL (rg_client_broken fr_RG) 1 a); [dt_infp | lia].
      + apply (KDG (rg_send_dead fr_RG) 1 a); [dt_infp | lia].
      + apply (KSL (rg_send_eintr fr_RG) 1 a); [dt_infp | lia].
    - revert Hr. destruct (Z.eqb_spec (lm_cap mc) 0) as [Ec | Ec]; intros Hr; cbn in Hr.
      + destruct Hr.
      + destruct Hr as [<- | []]. cbn [fst snd] in Ha.
        apply (KBLK (lm_out mc, lm_cap mc) a); [|cbn [fst snd]; lia].
        apply HAOR. unfold aout_blks. rewrite (proj2 (Z.eqb_neq (lm_cap mc) 0) Ec). left. reflexivity. }
  assert (HGONE2 : agone_at fr_RG W2 mem2 (lm_gn mc)).
  { apply (agone_at_kept fr_RG W mem W2 mem2 _ HGONE). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KDG (rg_gone fr_RG) 1 a); [dt_infp | lia]. }
  assert (HLOCK2 : alock_at fr_RG W2 mem2 false).
  { apply (alock_at_kept fr_RG W mem W2 mem2 _ HLOCK). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply KGL; [apply HGlock; lia | dt_num | dt_num]. }
  assert (HWAKE2 : awake_at fr_RG W2 mem2).
  { apply (awake_at_kept fr_RG W mem W2 mem2 HWAKE). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KDG (rg_wake fr_RG) 8 a); [dt_infp | lia]. }
  unfold amodel_ne. cbn [dc_setsrc lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [rewrite set_nth_length; exact Hlen4|].
  split; [exact HSL2|]. split; [exact HREL2|]. split; [exists ev2; exact HOUT2|].
  split; [exact HGONE2|]. split; [exact HLOCK2|]. split; [exact HWAKE2|].
  split; [apply (akept_vm W mem); [|exact HNFD]; intros x Hx; apply (KDG AG_NFD 4 x); [dt_infp | dt_num]|].
  split; [apply (akept_awr W mem); [|exact HNFDW]; intros x Hx; apply (KDG AG_NFD 4 x); [dt_infp | dt_num]|].
  split; [exact HNFDr|].
  split; [apply (akept_vm W mem); [|exact HTUP]; intros x Hx; apply (KDG AG_THREAD_UP 1 x); [dt_infp | dt_num]|].
  split; [destruct HLST as (lst & HL); exists lst; apply (akept_vm W mem); [|exact HL]; intros x Hx;
          apply (KDG AG_LISTEN 4 x); [dt_infp | dt_num]|].
  apply (akept_awr W mem); [|exact HLSTW]. intros x Hx. apply (KDG AG_LISTEN 4 x); [dt_infp | dt_num].
Qed.

(* cnl_spec's memmove bound on the held vector, `AREC * capb H E < 2 ^ 32`, at the source the call reads: the held
   vector is either empty or an allocator block, whose request is below MALLOC_MAX = 2 ^ 28 (al_blocks, the shape of
   lib/B/W_list_free.v lf_cap32 at a working branch), and the count bound gives the other term *)
Lemma dcE_capb : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h ->
  hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 ->
  AREC * capb (hs_held h) (hs_expected h) < 2 ^ 32.
Proof.
  intros ly S W mem md HA h HAR HSRC Hn.
  pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLH & _).
  pose proof HLH as (_ & _ & _ & _ & _ & Hvc & _).
  assert (Hcap : AREC * hl_cap (hs_held h) < 2 ^ 28).
  { destruct Hvc as [[Hc0 _] | (Hcp & Hin & _)]; [rewrite Hc0; unfold AREC; lia|].
    destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & _ & _ & _ & _ & _ & Hb).
    unfold MALLOC_MAX in Hb. lia. }
  pose proof (Zle_0_nat (count_begin (texts (hs_expected h)))) as Hcb.
  unfold capb. unfold AREC in *. lia.
Qed.

(* ---- stage E: 0x84920 addi a1,s1,192 ; mv a0,s5 ; jal check_no_loss -> 0x8492c.
   Contract: the kit's cnl_spec, lib/B/W_contract.v:2054 (cnl_post :1967, CNL_STK :1966 = 16640, Section w3n), at
   BASE + AF_fr_check_no_loss, taken through dre_CNL at G = [(HA + 64, 32)], the drained slot's two list headers
   (gx_ok from dre_HGs / HG, gx_rt from dre_HGs / dre_HERR_HI / dre_HAP, rom_out from dre_ROM_OUT); its memmove
   bound `AREC * capb .. < 2 ^ 32` (:2018) from dcE_capb above; its last premise, the caller's stack readable from
   sp up to ly_top (:2023), from dcF_stk_rd above (sp = F; the cut's STKR carried by the arm's journal); journal
   composition: dr_callZ above (ajournal_gx_sub, with the `at` cell F + 192 the out cell of the raised window
   XO = DR_XO = 208), then ajournal_gx_G_mono to G_fr. ---- *)
Lemma dc_stE : forall cx t m j si fpos FF ly S mc h1 W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (si < 4)%nat -> nth si (lm_hs mc) None = Some h1 ->
  NoDup (texts (hs_held h1)) -> hl_n (hs_expected h1) < 2 ^ 26 ->
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 ->
  cnl_room MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1))
    (hl_recs (hs_expected h1)) ->
  mo_ok MT S (cnl_cost MT (hs_expected h1) (hs_held h1)) ->
  (lm_gn mc = 0 -> exists rest, lm_O mc = bstream (hs_expected h1) ++ rest) ->
  dc_at cx t m j si fpos FF A_dr_r4 ly S mc false 0 1 W c ->
  SRr segs W c (fun W' c' => exists ly' S' E' H',
    dc_at cx t m j si fpos FF A_dr_r5 ly' S' (dc_setsrc mc si (set_exp_held h1 E' H')) false
      (if lm_gn mc =? 0 then Z.of_nat (length (bstream (hs_expected h1))) else 0) 1 W' c' /\
    mo_le MT S S' (cnl_cost MT (hs_expected h1) (hs_held h1)) /\
    dr_cfun h1 E' H').
Proof.
  intros cx t m j si fpos FF ly S mc h1 W c HB Hsi Hh1 HND HnE HnH HROOM HMO HOB
    (regs & mem & md & k & -> & HR & HJ & HFF & HCTX & SAT & HMOD & HSEP & HKY).
  pose proof HR as (HREGS & R23).
  pose proof HREGS as (R2 & R8 & R9 & R18 & R19 & R24 & R26 & R27 & R3 & R4 & R25 & Ht & R20 & R21 & R22).
  pose proof HCTX as (HFR & HFL & HIN & HRV & HROM & SVN).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : AR segs B ly S W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & _).
  destruct (dcF_F cx HB) as (HFb & HF32 & Ho16 & Hsp0 & Hnlen).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  destruct (dc_plain_entry A_dr_r4 W regs mem R27) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  clear HE.
  (* 0x84920-0x84928: addi a1,s1,192 ; mv a0,s5 ; jal check_no_loss *)
  paj_run_to_tok RUNTO HS HJ SHOK DRspan AF_fr_check_no_loss.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR3.
  cbn [ms_regs restrict] in KR3.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (23%bv : bv 5) Q23.
  rewrite (EEo 23%nat 23%bv eq_refl), R23 in Q23.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  (* ---- the call's registers ---- *)
  set (regsc := ms_regs ms) in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof dcE_vals as (Vnout & Vout & Vgone & Vs).
  assert (EASRC : ASRC = 96) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (EHA : HA = rg_s fr_RG + ASRC * Z.of_nat si) by reflexivity.
  assert (HFlo : DR_CEIL8 + 32000 <= F) by (unfold DR_CEIL8; lia).
  assert (Rc10 : getr regsc 10 = w64 HA) by (rewrite Q10, (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (Rc11 : getr regsc 11 = w64 (F + 192)).
  { rewrite Q11, (EEo 9%nat 9%bv eq_refl), R9. unfold w64. rewrite unsigned_lit_small by (unfold DR_CEIL8 in *; lia).
    reflexivity. }
  assert (Hspc : spZ regsc = F).
  { unfold spZ. rewrite (KR3 2%bv ltac:(dc_in)). exact Hsp. }
  assert (HJin : exists memS, ajournal segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly S W mem mdc k).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0. exists memS. exact HJ0. }
  destruct HJin as (memS & HJ0).
  pose proof HJ0 as (HARc & HLY & _ & _ & _ & HFRS0 & _ & _ & _ & _ & _ & _ & HJgone & HJpres & _).
  assert (Etop : ly_top ly = ly_top (c_ly cx)) by (pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (Hfin : In (1, fpos) (frames S)) by (rewrite HFRS0; left; reflexivity).
  (* ---- the model at the call ---- *)
  pose proof HMOD as (Hlen4 & HSL & HREL & (ev & HOUT) & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  assert (HSRC : asrc_at B ly S W mem HA h1) by (pose proof (HSL si Hsi) as X; rewrite Hh1 in X; exact X).
  assert (HCAPB : AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32) by exact (dcE_capb ly S W mem md HA h1 HAR HSRC HnH).
  pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLE & HLH & _).
  set (LE := list_blks (hs_expected h1)). set (LH := list_blks (hs_held h1)).
  set (PP := (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1)).
  set (OTH := concat (map slot_blks (firstn si (lm_hs mc) ++ skipn (Datatypes.S si) (lm_hs mc)))).
  set (ENT := concat (map aentry_blks (lm_es mc))).
  set (AO := aout_blks (lm_cap mc) (lm_out mc)).
  set (GE := [(lm_G mc, ATABLE)]).
  destruct HSEP as ((RS & HP0) & HSEP2).
  set (R := PP ++ input_blks cx ++ GE ++ ENT ++ OTH ++ AO ++ RS).
  assert (HCS : Permutation (concat (map slot_blks (lm_hs mc))) ((PP ++ LE ++ LH) ++ OTH)).
  { pose proof (dr_concat_nth_perm _ _ slot_blks (lm_hs mc) si None ltac:(lia)) as X. rewrite Hh1 in X. exact X. }
  assert (HP1 : Permutation (ablocks B ly S) ((LE ++ LH) ++ R)).
  { apply (Permutation_trans HP0).
    exact (dcE_perm_shape (input_blks cx) GE ENT OTH AO RS PP LE LH (concat (map slot_blks (lm_hs mc))) HCS). }
  assert (HND1 : List.NoDup ((LE ++ LH) ++ R)) by exact (Permutation_NoDup HP1 (dj_nodup ly S W mem md HAR)).
  assert (LEHin : forall b, In b (LE ++ LH) -> In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP1)). apply in_or_app. left. exact Hb. }
  assert (Rin : forall b, In b R -> In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP1)). apply in_or_app. right. exact Hb. }
  assert (RnLEH : forall b, In b R -> ~ In b (LE ++ LH)) by (intros b H1 H2; exact (dc_nd_app _ _ b HND1 H2 H1)).
  assert (CSmodel : forall b, In b (concat (map slot_blks (lm_hs mc))) -> In b (model_blks mc)).
  { intros b Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (H1CS : forall b, In b (PP ++ LE ++ LH) -> In b (concat (map slot_blks (lm_hs mc)))).
  { intros b Hb. apply in_concat. exists (slot_blks (Some h1)). split; [apply in_map; rewrite <- Hh1; apply nth_In; lia|].
    exact Hb. }
  assert (LEHmodel : forall b, In b (LE ++ LH) -> In b (model_blks mc)).
  { intros b Hb. apply CSmodel, H1CS. apply in_or_app. right. exact Hb. }
  (* ---- check_no_loss's G: slot si's two list headers ---- *)
  assert (HGcG : forall a, inG [(HA + 64, 32)] a -> inG G_fr a).
  { intros a Ha. apply dcE_inG1 in Ha. apply HGs. unfold HA, ASRC in *. lia. }
  assert (HGc : gx_ok segs B [(HA + 64, 32)]) by exact (gx_ok_sub segs B _ _ HGcG HG).
  assert (HGrt : gx_rt B [(HA + 64, 32)]).
  { intros a Ha. apply dcE_inG1 in Ha. destruct HAP as [HAP0 HAP30].
    unfold HA in Ha. split; [dt_num|]. split; lia. }
  assert (HRO : rom_out segs B [(HA + 64, 32)]).
  { intros a Ha. destruct (DR_ROM_OUT a Ha) as (H1 & H2 & H3 & H4).
    split; [intros HGa; exact (H1 (HGcG a HGa))|]. split; [exact H2|]. split; [exact H3 | exact H4]. }
  assert (HZc : azs B (HA + 64) 32).
  { destruct HZS as (r & Hr & H8 & H1 & H2). exists r. split; [exact Hr|]. split; [exact H8|].
    unfold HA, ASRC in *. split; lia. }
  (* ---- check_no_loss's premises ---- *)
  pose proof HOUT as (_ & _ & O3 & _ & _ & _ & O7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                      _ & _ & _ & _ & _ & _ & _ & O26).
  assert (HAOR : forall b, In b AO -> In b R)
    by (intros b Hb; unfold R; do 5 (apply in_or_app; right); apply in_or_app; left; exact Hb).
  assert (HPPR : forall b, In b PP -> In b R) by (intros b Hb; unfold R; apply in_or_app; left; exact Hb).
  assert (HOBX : ob_at W mem (lm_out mc) (lm_O mc) /\
     Z.of_nat (length (lm_O mc)) <= 2 ^ 40 /\ (0 < Z.of_nat (length (lm_O mc)) -> Z.of_nat (length (lm_O mc)) < 2 ^ 32) /\
     amem_range (lm_out mc) (Z.of_nat (length (lm_O mc)) + 8) /\
     (lm_O mc = [] \/ exists CO, Z.of_nat (length (lm_O mc)) <= CO /\ In (lm_out mc, CO) (ablocks B ly S) /\
        ~ In (lm_out mc) (hs_blocks h1))).
  { destruct O26 as [(Hc0 & Hout0 & Hno0) | (Hcp & Hno & Hin & junk & Hj & Hg)].
    - assert (HO0 : lm_O mc = []) by (apply length_zero_iff_nil; lia).
      rewrite HO0, Hout0. cbn [length]. split; [intros i Hi; cbn in Hi; lia|].
      split; [lia|]. split; [lia|]. split; [left; unfold kLowMemEnd; lia | left; reflexivity].
    - destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & _ & _ & Happ & _ & _ & Hmx).
      assert (Ers : req_size (lm_cap mc) = lm_cap mc)
        by (unfold req_size; rewrite (proj2 (Z.eqb_neq (lm_cap mc) 0) ltac:(lia)); reflexivity).
      rewrite Ers in Happ. unfold MALLOC_MAX in Hmx.
      split; [exact (dcE_ob_at W mem _ _ _ Hg)|].
      split; [lia|]. split; [lia|].
      split; [zlia|].
      right. exists (lm_cap mc). split; [lia|]. split; [exact Hin|].
      intros Hx. destruct (dcE_hs_blocks h1 _ Hx) as (n & Hn).
      assert (HnPP : In (lm_out mc, n) (PP ++ LE ++ LH)) by exact Hn.
      assert (HAOc : In (lm_out mc, lm_cap mc) AO)
        by (unfold AO, aout_blks; rewrite (proj2 (Z.eqb_neq (lm_cap mc) 0) ltac:(lia)); left; reflexivity).
      assert (Hn1 : In (lm_out mc, n) (ablocks B ly S)).
      { apply in_app_or in HnPP as [Hp | Hp]; [exact (Rin _ (HPPR _ Hp)) | exact (LEHin _ Hp)]. }
      destruct (dc_dec (lm_out mc, n) (lm_out mc, lm_cap mc)) as [Heq | Hne].
      + rewrite Heq in HnPP. apply in_app_or in HnPP as [Hp | Hp].
        * apply (dc_nd_app PP (input_blks cx ++ GE ++ ENT ++ OTH ++ AO ++ RS) (lm_out mc, lm_cap mc)
            (dc_nd_r _ _ HND1) Hp). do 4 (apply in_or_app; right). apply in_or_app. left. exact HAOc.
        * exact (RnLEH _ (HAOR _ HAOc) Hp).
      + destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hn1) as (_ & _ & _ & _ & _ & _ & Hn0).
        pose proof (req_size_pos n ltac:(lia)) as [Hr1 _]. pose proof (req_size_pos (lm_cap mc) ltac:(lia)) as [Hr2 _].
        exact (dj_apart ly S W mem md _ _ _ _ (lm_out mc) HAR Hin Hn1 (fun E => Hne (eq_sym E)) ltac:(lia) ltac:(lia)). }
  destruct HOBX as (HOBAT & HNO40 & HNO32 & HMR & HOB0). clear O26.
  assert (P5 : forall a, spZ regsc <= a < spZ regsc + 208 -> apresent (w_H W) mem a).
  { intros a Ha. apply HJpres. rewrite Hspc in Ha. unfold LLVMF_STK. lia. }
  assert (P21 : val_mem segs (arm W mem) (VAL A_g_gone) 1 (lm_gn mc)) by (rewrite Vgone; exact (proj1 HGONE)).
  assert (P22 : 0 <= lm_gn mc < 256) by (destruct HGONE as (_ & _ & [G0 | G0]); lia).
  assert (P23 : val_mem segs (arm W mem) (VAL A_g_nout) 8 (Z.of_nat (length (lm_O mc)))) by (rewrite Vnout; exact O3).
  assert (P24 : val_mem segs (arm W mem) (VAL A_g_out) 8 (lm_out mc)) by (rewrite Vout; exact O7).
  assert (HF8 : (F + 192) mod 8 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (F / 32) + 192) with ((4 * (F / 32) + 24) * 8) by ring. apply Z_mod_mult. }
  (* ---- check_no_loss's afn_pre at sp = F ---- *)
  destruct (dr_afn_pre_at cx ly S fpos k W mem mdc regsc CNL_STK HB HJ) as (ch & HPREc).
  { rewrite HFF. exact HFR. }
  { exact Hspc. }
  { rewrite Q1. apply ret_ok_codeptr_v; [unfold A_dr_r5, AF_arm_drain; lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by (unfold A_dr_r5, AF_arm_drain; lia).
    unfold A_dr_r5, AF_arm_drain; lia. }
  { rewrite (KR3 3%bv ltac:(dc_in)). exact R3. }
  { rewrite (KR3 4%bv ltac:(dc_in)). exact R4. }
  { rewrite (KR3 8%bv ltac:(dc_in)). exact R8. }
  { rewrite dcE_cnl_stk. lia. }
  { rewrite dcE_cnl_stk. unfold LLVMF_STK. lia. }
  assert (P4 : spZ regsc + 208 <= ly_top ly) by (rewrite Hspc, Etop; lia).
  assert (P8 : HA = VAL A_g_s + ASRC * Z.of_nat si) by (rewrite Vs; reflexivity).
  assert (P11 : spZ regsc <= F + 192) by (rewrite Hspc; lia).
  assert (P12 : F + 192 + 8 <= spZ regsc + 208) by (rewrite Hspc; lia).
  assert (P14 : forall a, HA + 64 <= a < HA + 96 -> inG [(HA + 64, 32)] a) by (intros a Ha; apply dcE_inG1; lia).
  pose proof (dcE_lit W mem _ _ HRV (proj1 dcE_lits)) as L1.
  pose proof (dcE_lit W mem _ _ HRV (proj1 (proj2 dcE_lits))) as L2.
  pose proof (dcE_lit W mem _ _ HRV (proj2 (proj2 dcE_lits))) as L3.
  assert (P20 : 0 <= 0 <= Z.of_nat (length (lm_O mc))) by lia.
  (* cnl_spec's last premise (W_contract.v:2087): the stack readable from sp = F up to ly_top *)
  assert (HSTK : forall a, spZ regsc <= a < ly_top ly -> aview segs (w_H W) mem a <> None).
  { intros a Ha. rewrite Hspc in Ha. exact (dcF_stk_rd cx ly S fpos W mem mdc k HB HJ a Ha). }
  (* ---- the call ---- *)
  set (FPc := blk_FP (LE ++ LH)).
  set (K := fun (ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word)
      (mem2 : word -> option byte) (md2 : Model) =>
    exists kk (E' H' : hlist),
      ajournal_gx segs B [(HA + 64, 32)] 208 [(F + 192, F + 192 + 8)] CNL_STK (spZ regsc) FPc
        ly S W mem mdc [] ly2 S2 W2 mem2 md2 kk /\
      asrc_at B ly2 S2 W2 mem2 HA (set_exp_held h1 E' H') /\
      hl_recs E' = [] /\ hl_v E' = hl_v (hs_expected h1) /\ hl_cap E' = hl_cap (hs_expected h1) /\
      NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h1)) (texts (hs_expected h1)) /\
      val_mem segs (arm W2 mem2) (F + 192) 8
        (if lm_gn mc =? 0 then 0 + Z.of_nat (length (bstream (hs_expected h1))) else 0) /\
      (forall rest, Permutation (ablocks B ly S) (LE ++ LH ++ rest) ->
         Permutation (ablocks B ly2 S2) (list_blks E' ++ list_blks H' ++ rest)) /\
      mo_le MT S S2 (cnl_cost MT (hs_expected h1) (hs_held h1))).
  eapply SRr_mono.
  { apply (dr_callZ G_fr W regsc mem (Z_to_bv 64 (BASE + AF_fr_check_no_loss)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S mdc k CNL_STK FPc 208
      [(F + 192, F + 192 + 8)] (F - sp0) (getr regsc 1) ch K HG HJ).
    - rewrite Hspc. lia.
    - lia.
    - rewrite dcE_cnl_stk. unfold LLVMF_STK. lia.
    - lia.
    - lia.
    - intros a (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold LLVMF_STK. lia.
    - reflexivity.
    - exact HPREc.
    - eapply SRr_mono.
      { exact (CNL [(HA + 64, 32)] HGc HGrt HRO W ly S regsc mem mdc ch 208 HA si (F + 192) h1 (lm_gn mc) 0
          (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)
          HPREc ltac:(lia) eq_refl P4 P5 Rc10 Rc11 P8 Hsi HF8 P11 P12 HSRC P14 HZc
          HND HnE HnH SAT P20 P21 P22 P23 P24 HOBAT eq_refl HNO40 HNO32 HMR HOB0 HOB HRV L1 L2 L3 HROOM HMO
          HCAPB HSTK). }
      (* the kit's cnl_post carries errno's view after apres_kept (W_contract.v:2032); this stage re-reads errno *)
      cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & kk & E' & H' & -> & JC & HPR & HPK & _ & HSRC2 & ER &
        EV' & EC & HNDH & HTX & HCAPH & MAT & MGN & MNO & MOUT & HOB2 & HPERM & HFRS & HMO2 & _ & _).
      exists ly2, S2, regs2, mem2, md2, kk. split; [reflexivity|].
      split; [eapply ajournal_gx_G_mono; [exact HGcG | exact JC]|].
      split; [exact HPR|].
      unfold K. exists kk, E', H'. split; [exact JC|]. split; [exact HSRC2|].
      do 5 (split; [assumption|]). split; [exact MAT|]. split; [exact HPERM | exact HMO2].
    - intros a (r & Hr & Hra). unfold FPc, blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst snd] in Hra.
      pose proof (LEHin _ Hb) as Hbl.
      destruct (in_dec dc_dec (p, n) (ablocks B (c_ly cx) (c_S cx))) as [Hc | Hc].
      + left. destruct (HSEP2 _ (LEHmodel _ Hb)) as [Hn | Hfp]; [exfalso; exact (Hn Hc)|].
        split; [exact (Hfp a Hra)|].
        exists p, n. split; [exact Hbl | exact Hra].
      + right. exists p, n. split; [exact Hbl|]. split; [exact Hc | exact Hra]. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HPR2 & HK2).
  unfold K in HK2. destruct HK2 as (kk & E' & H' & JC & HSRC2 & ER & EV' & EC & HNDH & HTX & MAT & HPERM & HMO2).
  rewrite Hspc in JC. clear HOB0.
  assert (AR2 : AR segs B ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR; exact JC).
  set (h' := set_exp_held h1 E' H') in *.
  set (LE' := list_blks E'). set (LH' := list_blks H').
  assert (HP2 : Permutation (ablocks B ly2 S2) ((LE' ++ LH') ++ R)).
  { rewrite <- app_assoc. apply HPERM. rewrite app_assoc. exact HP1. }
  assert (HND2 : List.NoDup ((LE' ++ LH') ++ R)) by exact (Permutation_NoDup HP2 (dj_nodup ly2 S2 W2 mem2 md2 AR2)).
  assert (Rin2 : forall b, In b R -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. exact Hb. }
  assert (LEHin2 : forall b, In b (LE' ++ LH') -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. left. exact Hb. }
  (* ---- what check_no_loss keeps ---- *)
  pose proof (dcE_kept_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KB0.
  pose proof (dcE_kept_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KI0.
  pose proof (dcE_kept_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KF0.
  assert (KBLK : forall b a, In b R -> fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem2 a).
  { intros [p n] a HbR Ha. cbn [fst snd] in Ha. pose proof (Rin _ HbR) as Hin1.
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin1) as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hrs].
    exact (KB0 p n a Hin1 (Rin2 _ HbR) (RnLEH _ HbR) ltac:(lia)). }
  assert (HOi : forall i b, (i < 4)%nat -> i <> si -> In b (slot_blks (nth i (lm_hs mc) None)) -> In b R).
  { intros i b Hi Hne Hb. assert (Hb' : In b OTH).
    { unfold OTH. apply in_concat. exists (slot_blks (nth i (lm_hs mc) None)). split; [|exact Hb].
      apply in_map. apply dc_in_rm_nth; [rewrite Hlen4; exact Hi | exact Hne]. }
    unfold R. do 4 (apply in_or_app; right). apply in_or_app. left. exact Hb'. }
  assert (HGER : forall b, In b (arelay_blks (lm_G mc) (lm_es mc)) -> In b R).
  { intros b [<- | Hb]; unfold R.
    - do 2 (apply in_or_app; right). apply in_or_app. left. unfold GE. left. reflexivity.
    - do 3 (apply in_or_app; right). apply in_or_app. left. exact Hb. }
  pose proof (dcE_model_kept ly S W mem ly2 S2 W2 mem2 md2 mc si h' R HA AR2 Hsi EHA HMOD HKY HSRC2 HOi HGER HAOR
    Rin2 KBLK KI0) as HMOD2.
  (* ---- the blocks after the call ---- *)
  assert (HCS' : Permutation (concat (map slot_blks (set_nth si (Some h') (lm_hs mc)))) ((PP ++ LE' ++ LH') ++ OTH))
    by exact (dr_concat_set_nth_perm _ _ slot_blks (lm_hs mc) si (Some h') ltac:(lia)).
  assert (HP3 : Permutation (input_blks cx ++ model_blks (dc_setsrc mc si h') ++ RS) ((LE' ++ LH') ++ R))
    by exact (dcE_perm_shape (input_blks cx) GE ENT OTH AO RS PP LE' LH' _ HCS').
  assert (HSEP' : ablocks_sep B fr_FP cx (dc_setsrc mc si h') ly2 S2).
  { split; [exists RS; exact (Permutation_trans HP2 (Permutation_sym HP3))|].
    intros b Hb.
    assert (Hcase : In b (LE' ++ LH') \/ In b (model_blks mc)).
    { unfold model_blks in Hb. cbn [dc_setsrc lm_G lm_es lm_hs lm_cap lm_out] in Hb.
      destruct Hb as [<- | Hb]; [right; unfold model_blks; left; reflexivity|].
      apply in_app_or in Hb as [Hb | Hb]; [right; unfold model_blks; right; apply in_or_app; left; exact Hb|].
      apply in_app_or in Hb as [Hb | Hb];
        [|right; unfold model_blks; right; apply in_or_app; right; apply in_or_app; right; exact Hb].
      apply (Permutation_in _ HCS') in Hb. apply in_app_or in Hb as [Hb | Hb].
      - apply in_app_or in Hb as [Hb | Hb]; [right; apply CSmodel, H1CS, in_or_app; left; exact Hb | left; exact Hb].
      - right. apply CSmodel. unfold OTH in Hb. apply in_concat in Hb as (l & Hl & Hbl). apply in_concat.
        exists l. split; [|exact Hbl]. apply in_map_iff in Hl as (o & <- & Ho). apply in_map.
        exact (dr_in_rm _ si o (lm_hs mc) Ho). }
    destruct Hcase as [Hnew | Hold]; [|exact (HSEP2 b Hold)].
    destruct (in_dec dc_dec b (ablocks B (c_ly cx) (c_S cx))) as [Hc | Hc]; [|left; exact Hc]. right.
    destruct (in_dec dc_dec b (ablocks B ly S)) as [Hb1 | Hb1].
    - apply (Permutation_in _ HP1) in Hb1. apply in_app_or in Hb1 as [Hb1 | Hb1].
      + destruct (HSEP2 b (LEHmodel b Hb1)) as [Hn | Hfp]; [exfalso; exact (Hn Hc) | exact Hfp].
      + exfalso. exact (dc_nd_app _ _ b HND2 Hnew Hb1).
    - destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      replace a with (p + (a - p)) by lia. exact (HJgone p n (a - p) Hc Hb1 ltac:(lia)). }
  (* ---- the frame, the input, the ROM, the cells ---- *)
  assert (KOUT : forall a, F <= a < sp0 -> ~ (F + DR_AT <= a < F + DR_AT + 8) -> abyte_kept W mem W2 mem2 a).
  { intros a Ha Hn. unfold DR_AT in Hn.
    apply (dcE_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HGc JC).
    - unfold DR_CEIL8 in *. lia.
    - rewrite dcE_inG1. unfold DR_CEIL8 in *. dt_num.
    - intros Hi. pose proof (Hsegs a Hi). unfold DR_CEIL8 in *. lia.
    - destruct (Z_lt_le_dec a (F + 208)) as [Hlt | Hge].
      + right; left. split; [lia|]. intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
      + left. unfold DR_CEIL8 in *. split; [lia|]. rewrite dcE_cnl_stk. lia. }
  assert (WF : forall a, F <= a < sp0 -> writable_at segs (arm W2 mem2) a).
  { intros a Ha. apply (apresent_writable segs).
    exact (dcF_pres cx fpos ly2 S2 W2 mem2 md2 (k + k1) HJ2 a ltac:(unfold LLVMF_STK; lia)). }
  assert (KFF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. apply (KF0 1 fpos a Hfin). left. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite HFF. replace (fs_frame_bytes 1) with 128 by reflexivity. lia. }
  assert (KSH : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. apply (KF0 1 fpos a Hfin). right. unfold in_zr. cbn [fst snd].
    rewrite HFF. replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr.
    unfold SB, SHADOW_OFF in *. lia. }
  assert (H320 : lf_F cx + 320 <= spZ (c_regs cx)) by (change (F + 320 <= sp0); lia).
  assert (HFR2 : aframe_at cx FF W2 mem2) by exact (dc_aframe_kept cx FF W W2 mem mem2 HFR H320 KOUT WF KFF KSH).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly 1 fpos))
    by (apply (dr_sv8_kept W W2 mem mem2); [intros x Hx; apply KFF; lia | exact HFL]).
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { destruct HIN as (Hcase & Hg).
    assert (HINR : c_n cx <> 0 -> In (c_p cx, c_n cx) R).
    { intros Hn0. unfold R. apply in_or_app. right. apply in_or_app. left. unfold input_blks.
      rewrite (proj2 (Z.eqb_neq (c_n cx) 0) Hn0). left. reflexivity. }
    split.
    - destruct Hcase as [Hc | (Hn & Hin)]; [left; exact Hc | right; split; [exact Hn|]].
      exact (Rin2 _ (HINR ltac:(lia))).
    - apply (akept_garr8 W mem); [|exact Hg]. intros x Hx. rewrite length_map in Hx.
      destruct Hcase as [(Hc & _) | (Hn & Hin)].
      + lia.
      + apply (KBLK (c_p cx, c_n cx) x (HINR ltac:(lia))). cbn [fst snd]. lia. }
  assert (HRV2 : rom_view segs W2 mem2)
    by exact (ajournal_gx_rom_view segs B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ JC HRO HRV).
  assert (HROM2 : jt_rom W2 mem2) by exact (dt_jt_kept W W2 mem mem2 HRV HRV2 HROM).
  assert (SVN2 : sv8 W2 mem2 (F + DR_N) (c_n cx - dr_k' cx m)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact SVN]. intros x Hx. apply KOUT; unfold DR_N, DR_AT in *; lia. }
  assert (SAT2 : sv8 W2 mem2 (F + DR_AT) (if lm_gn mc =? 0 then Z.of_nat (length (bstream (hs_expected h1))) else 0)).
  { replace (0 + Z.of_nat (length (bstream (hs_expected h1)))) with (Z.of_nat (length (bstream (hs_expected h1))))
      in MAT by lia. exact MAT. }
  destruct (dcF_frame_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos JC) as (Efr & Efl).
  (* ---- the state at 0x8492c ---- *)
  exists ly2, S2, E', H'.
  split; [|split; [exact HMO2 | split; [exact ER | split; [exact EV' | split; [exact EC | split; [exact HNDH | exact HTX]]]]]].
  exists regs2, mem2, md2, (k + k1).
  split; [rewrite Q1; reflexivity|].
  split.
  { assert (P23' : getr regs2 23 = w64 1)
      by (rewrite (dj_pres regsc regs2 23%bv HPR2 ltac:(dj_cs)); exact Q23).
    exact (dcF_regs_kept cx t m j si FF 1 1 regs regs2
             (fun r Hr => eq_trans (dcF_pres_K regsc regs2 HPR2 r Hr) (KR3 r Hr)) P23' HR). }
  split; [exact HJ2|].
  split; [rewrite Efr; exact HFF|].
  split; [rewrite Efl; exact (conj HFR2 (conj HFL2 (conj HIN2 (conj HRV2 (conj HROM2 SVN2)))))|].
  split; [exact SAT2|].
  split; [exact HMOD2|]. split; [exact HSEP' | exact HKY].
Qed.

(* ---- stage F: 0x8492c ld a0,192(s1) ; jal check_shape_done -> 0x84934 ; j 84804 (the latch).
   Contract: lib/B/W_contract.v:157 csd_spec at BASE + AF_fr_check_shape_done (dre_CSD) - aleaf_post, whose
   errno-view conjunct (:112) this stage does not need;
   journal composition: dr_callZ above (ajournal_gx_sub), then the plain run of `j 84804` (W_journal.v
   paj_run_to_x).  B's arm has no join block: s9 = t and s4 = the cursor are already the latch's (image A
   reloads s9 from F+104 in its join), and s7 = 1 since 0x84910. ---- *)
Lemma dc_stF : forall cx t m j si fpos FF ly S mc W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  dr_at_op cx m ->
  (forall ev, RINV cx (t + 1) (dc_fin cx m mc ev)) -> (forall ev, LS cx (t + 1) (dc_fin cx m mc ev) ly S) ->
  dc_at cx t m j si fpos FF A_dr_r5 ly S mc false (Z.of_nat (length (lm_O mc))) 1 W c ->
  SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t m j si fpos FF ly S mc W c HB Hatop HRI HLS
    (regs & mem & md & k & -> & HR & HJ & HFF & HCTX & SAT & HNE & HSEP & HKB).
  pose proof HR as (HREGS & R23).
  pose proof HREGS as (R2 & R8 & R9 & R18 & R19 & R24 & R26 & R27 & R3 & R4 & R25 & Ht & R20 & R21 & R22).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  destruct (dcF_F cx HB) as (HFb & HF32 & Ho16 & Hsp0 & Hnlen).
  assert (HAR : AR segs B ly S W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof (dcF_fin cx fpos ly S W mem md k HJ) as Hfin.
  assert (Hk' : 0 <= dr_k' cx m <= c_n cx) by (pose proof Hatop as (Hk0 & _ & _); exact (dr_k'_rng cx m Hk0)).
  (* at = |O| = g_nout *)
  pose proof HNE as (_ & _ & _ & (ev0 & HOUT0) & _).
  destruct HOUT0 as (_ & _ & HNO & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     _ & Hcap).
  unfold arm in HNO.
  assert (HA : 0 <= Z.of_nat (length (lm_O mc)) < 2 ^ 64).
  { destruct Hcap as [(_ & _ & Hz) | (Hc0 & Hle & Hin & _)]; [lia|].
    destruct (dr_blk ly S W mem md _ _ HAR Hin) as (Hb1 & Hb2 & Hb3). lia. }
  pose proof dcE_vals as (VN & _ & _ & _).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  set (NO := Z.of_nat (length (lm_O mc))) in *.
  (* 0x8492c-0x84930: ld a0,192(s1) ; jal check_shape_done *)
  destruct (dc_cell_entry A_dr_r5 192 W regs mem F NO R9 R27 ltac:(lia) ltac:(lia) HF32
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) SAT HA) as [HS SHOK].
  remember (Eimg (Ereg regs (dc_cell_extra NO))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (dc_cell_extra NO)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E32 : ew E 32 = Z_to_bv 64 NO)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  clear HE.
  paj_run_to_tok RUNTO HS HJ SHOK DRspan AF_fr_check_shape_done.
  { unfold ss_dc_cell. cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [dc_cell YP09.r_wlo YP09.r_whi] in Ha. lia. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (23%bv : bv 5) Q23.
  rewrite E32 in Q10. rewrite (EEo 23%nat 23%bv eq_refl), R23 in Q23.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dr_r6)) by exact Q1.
  destruct (dr_afn_pre_at cx ly S fpos k W mem md1 regs1 CSD_STK HB HJ
              ltac:(rewrite HFF; exact (proj1 HCTX)) Hsp1
              ltac:(rewrite Q1'; exact (ret_ok_codeptr_v A_dr_r6 ltac:(unfold A_dr_r6, AF_arm_drain; lia) eq_refl))
              ltac:(unfold raZ; rewrite Q1', unsigned_lit_small; unfold A_dr_r6, AF_arm_drain; lia)
              ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
              ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
              ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
              ltac:(unfold CSD_STK; lia) ltac:(unfold CSD_STK, LLVMF_STK; lia)) as (ch & HPRE1).
  eapply SRr_bind.
  { eapply (dr_callZ G_fr W regs1 mem (Z_to_bv 64 (BASE + AF_fr_check_shape_done)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S md1 k CSD_STK [] 0 [] (F - sp0)
      (Z_to_bv 64 (BASE + A_dr_r6)) ch
      (fun ly2 S2 W2 _ mem2 md2 => ly2 = ly /\ S2 = S /\ ajournal segs B CSD_STK F [] ly S W mem md1 [] ly S W2 mem2 md2 0)
      HG HJ ltac:(rewrite Hsp1; lia) ltac:(lia) ltac:(unfold CSD_STK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
      ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) Q1' HPRE1).
    - eapply SRr_mono;
        [exact (CSD W ly S regs1 mem md1 ch NO HPRE1 Q10 HA ltac:(rewrite VN; exact HNO))|].
      cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & _).
      rewrite Hsp1 in HJc.
      exists ly, S, regs2, mem2, md2, 0.
      split; [rewrite Q1'; reflexivity|].
      split; [rewrite Hsp1; apply (ajournal_gx_G_mono segs B [] G_fr);
              [intros a Ha; exfalso; exact (inG_nil a Ha) | apply ajournal_gx_nil; exact HJc]|].
      split; [exact HP2|]. split; [reflexivity|]. split; [reflexivity|]. exact HJc.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  (* back at 0x84934 *)
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HP2 & (-> & -> & HJp)).
  pose proof (dj_ne_plain ly S W W2 mem mem2 md1 md2 mc false CSD_STK F HJp
                ltac:(unfold CSD_STK; lia) HKB HNE) as HNE2.
  destruct (dj_ctx_plain cx m FF (flag_addr ly 1 fpos) ly S W W2 mem mem2 md1 md2 CSD_STK HB HJp
              ltac:(unfold CSD_STK; lia) (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX)
    as ((HFR2 & HFL2 & HIN2 & HRV2 & HJT2 & SVN2) & _).
  assert (P23 : getr regs2 23 = w64 1)
    by (rewrite (dj_pres regs1 regs2 23%bv HP2 ltac:(dj_cs)); exact Q23).
  pose proof (dcF_regs_kept cx t m j si FF 1 1 regs regs2
                (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HP2 r Hr) (KR r Hr)) P23 HR) as DR2.
  pose proof DR2 as ((R2' & R8' & R9' & R18' & R19' & R24' & R26' & R27' & R3' & R4' & R25' & Ht' & R20' & R21' & R22')
                     & R23').
  (* 0x84934: j 84804, onto the latch *)
  destruct (dc_plain_entry A_dr_r6 W2 regs2 mem2 R27') as [HS2 SHOK2].
  remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (HAE2 : env_agree 32 (Ereg regs2 []) E2)
    by (rewrite HE2; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE2.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 DRspan AF_LLVM_latch.
  { apply awr_ok_x_nil. }
  dr_meq HF Em2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
                HS2 HAE2 ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  pmkst HS2. rewrite Em2 in *.
  destruct HNE2 as (N1 & N2 & N3 & (ev & N4) & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HJT2|].
  exists [(1, fpos)], ly, S, (k + k1), (dc_fin cx m mc ev), fpos.
  split; [exact HJ2|]. split; [reflexivity|]. split; [rewrite HFF; exact HFR2|].
  split; [rewrite HFF; exact HFL2|].
  split; [exact (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj N7 (conj N8 (conj N9 (conj N10
                   (conj N11 (conj N12 N13))))))))))))|].
  split; [exact HIN2|]. split; [exact HRV2|].
  split; [exact HSEP|]. split; [exact (HLS ev)|]. split; [exact (HRI ev)|].
  rewrite HFF.
  split.
  { split; [rewrite (KR2 2%bv ltac:(cbv; tauto)); exact R2'|].
    split; [rewrite (KR2 8%bv ltac:(cbv; tauto)); exact R8'|].
    split; [rewrite (KR2 9%bv ltac:(cbv; tauto)); exact R9'|].
    split; [rewrite (KR2 18%bv ltac:(cbv; tauto)); exact R18'|].
    split; [rewrite (KR2 19%bv ltac:(cbv; tauto)); exact R19'|].
    split; [rewrite (KR2 23%bv ltac:(cbv; tauto)); exact R23'|].
    split; [rewrite (KR2 24%bv ltac:(cbv; tauto)); exact R24'|].
    split; [rewrite (KR2 26%bv ltac:(cbv; tauto)); exact R26'|].
    split; [rewrite (KR2 27%bv ltac:(cbv; tauto)); exact R27'|].
    split; [rewrite (KR2 3%bv ltac:(cbv; tauto)); exact R3'|].
    rewrite (KR2 4%bv ltac:(cbv; tauto)); exact R4'. }
  split; [rewrite (KR2 25%bv ltac:(cbv; tauto)); exact R25'|].
  split; [exact Ht'|].
  split; [rewrite (KR2 20%bv ltac:(cbv; tauto)); exact R20'|].
  split; [exact SVN2 | exact Hk'].
Qed.

(* ================================================================== the stage: the six calls, composed *)
Theorem dr_stage_calls : forall cx t m j si h fpos ly3 S3 k W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  DLK B G_fr fr_FP LS RINV cx t m j si h fpos ly3 S3 k W c ->
  SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t m j si h fpos ly3 S3 k W c HB HD.
  pose proof HD as (regs & mem & md & -> & HJ & HFR & HFL & HMOD & HIN & HRV & HROM & HSEP & HLS & HRI & Hatop &
                    Hpick & Hj & Hfdj & Hef0 & _).
  pose proof HMOD as (Hlen4 & _ & _ & _ & (_ & _ & Hgn01) & _).
  pose proof Hpick as (_ & Hsi & Hhsi).
  pose proof Hatop as (_ & HO0 & _).
  assert (HST : dc_static cx t m j si h) by exact (conj Hatop (conj Hpick (conj Hj (conj Hfdj (conj Hef0 HRI))))).
  set (FF := frame_addr ly3 1 fpos).
  (* lock *)
  eapply SRr_bind; [exact (dc_stA cx t m j si h fpos ly3 S3 k W _ HB HD)|]. intros W1 c1 _ H1.
  (* drain *)
  eapply SRr_bind; [exact (dc_stB cx t m j si h fpos FF ly3 S3 W1 c1 HB HST HLS H1)|].
  intros W2 c2 _ (ly4 & S4 & e' & h' & out' & ev' & LB & H2 & HMO1 & HDF).
  (* unlock *)
  eapply SRr_bind; [exact (dc_stC cx t m j si fpos FF ly4 S4 _ W2 c2 HB H2)|]. intros W3 c3 _ H3.
  set (m1 := dr_m1 m j si h h' e' ev' LB out') in *.
  pose proof HDF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 &
                     D19 & D20 & D21 & D22).
  assert (Hh1 : nth si (lm_hs m1) None = Some h').
  { unfold m1, dr_m1, dr_step. cbn [lm_hs]. apply set_nth_same. lia. }
  (* check_no_loss_read *)
  eapply SRr_bind; [exact (dc_stD cx t m j si fpos FF ly4 S4 m1 h' W3 c3 HB Hsi Hh1 D14 H3)|]. intros W4 c4 _ H4.
  destruct (RI_src cx t m si h HRI Hpick) as (Hexp0 & _ & _).
  destruct (LS_cnl_pre cx t m ly3 S3 ly4 S4 si h j h' HLS HRI Hpick Hj Hfdj Hef0 HMO1 D22 D17 D18)
    as (N1 & N2 & N3 & N4 & N5).
  (* the stream after the drain is the expected lines' bytes, when the controller is there *)
  assert (HBS : bstream (hs_expected h') = LB) by (rewrite Hexp0 in D17; exact (dc_bstream_LB _ _ LB D17 D21)).
  destruct (RI_gone cx t m HRI) as (G0 & G1).
  assert (HOB : lm_gn m1 = 0 -> exists rest, lm_O m1 = bstream (hs_expected h') ++ rest).
  { intros Hg. exists []. rewrite app_nil_r, HBS. cbn [m1 dr_m1 dr_step lm_gn lm_O] in Hg |- *. unfold dr_O1.
    rewrite HO0. cbn [app]. destruct (G0 Hg) as (C3 & C0 & D0).
    unfold dr_live, sl_live, send_line_c.send_live, send_line_c.send_off. rewrite C3, C0, D0. cbn.
    destruct (Z.eqb_spec (dr_tot h) 0) as [Ht0 | Ht0]; cbn; [|reflexivity].
    pose proof (dc_LB_len LB _ D21) as HL. unfold dr_tot in Ht0. rewrite Ht0 in HL.
    destruct LB; [reflexivity | cbn [length] in HL; lia]. }
  (* check_no_loss *)
  eapply SRr_bind; [exact (dc_stE cx t m j si fpos FF ly4 S4 m1 h' W4 c4 HB Hsi Hh1 N1 N2 N3 N4 N5 HOB H4)|].
  intros W5 c5 _ (ly6 & S6 & E' & H' & H5 & HMO2 & HCF).
  set (m2 := dc_setsrc m1 si (set_exp_held h' E' H')) in *.
  (* the at cell: |bstream| when the controller is there, 0 else; g_nout: |O1| *)
  assert (HA : (if lm_gn m1 =? 0 then Z.of_nat (length (bstream (hs_expected h'))) else 0) =
               Z.of_nat (length (lm_O m2))).
  { cbn [m2 dc_setsrc m1 dr_m1 dr_step lm_gn lm_O]. unfold dr_O1. rewrite HO0. cbn [app].
    destruct Hgn01 as [Hg | Hg]; rewrite Hg; cbn [Z.eqb].
    - destruct (HOB ltac:(cbn [m1 dr_m1 dr_step lm_gn]; exact Hg)) as (rest & Hr).
      cbn [m1 dr_m1 dr_step lm_O] in Hr. unfold dr_O1 in Hr. rewrite HO0 in Hr. cbn [app] in Hr.
      rewrite HBS. destruct (dr_live (lm_c m) h); [reflexivity|].
      rewrite HBS in Hr. destruct LB; [reflexivity | cbn in Hr; discriminate].
    - assert (Hlv : dr_live (lm_c m) h = false).
      { destruct (G1 Hg) as [C | [C | C]]; unfold dr_live, sl_live, send_line_c.send_live, send_line_c.send_off;
          rewrite C; cbn; [reflexivity | rewrite orb_true_r; reflexivity | rewrite andb_false_r; reflexivity]. }
      rewrite Hlv. reflexivity. }
  rewrite HA in H5.
  assert (Hfin : forall ev, dc_fin cx m m2 ev =
    dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' (dr_ctl (lm_c m) h ev) (dr_O1 m h LB) (dr_cap1 m j h) out').
  { intros ev. unfold dc_fin, m2, dc_setsrc, m1, dr_m1, dr_step.
    cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    rewrite dc_set_nth_twice, dc_ctl_dr. reflexivity. }
  (* check_shape_done and the latch *)
  apply (dc_stF cx t m j si fpos FF ly6 S6 m2 W5 c5 HB Hatop).
  - intros ev. rewrite Hfin.
    apply (RI_drain_step cx t m si h j e' h' (dr_ctl (lm_c m) h ev) (dr_O1 m h LB) (dr_cap1 m j h) out' ev LB E' H'
             HRI Hatop Hpick Hj Hfdj Hef0).
    unfold dr_step_ok. cbv zeta.
    destruct HCF as (F1 & F2 & F3 & F4 & F5).
    repeat (split; [assumption|]). split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    repeat (split; [assumption|]). exact F5.
  - intros ev. rewrite Hfin.
    exact (LS_drain_step cx t m ly3 S3 S4 ly6 S6 si h j (set_exp_held h' E' H') e' (dr_ctl (lm_c m) h ev)
             (dr_O1 m h LB) (dr_cap1 m j h) out' (hs_expected h') (hs_held h') HLS Hpick Hj HMO1 HMO2).
  - exact H5.
Qed.
End dr.
