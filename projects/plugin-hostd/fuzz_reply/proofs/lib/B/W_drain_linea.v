(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: la_callS is ported from the w4 lane's gx_callS, itself the cgif donor's
   cl_callS (proofs/cgif/*/lib/YC85.v:383, Anthropic PBC); the rest is new. *)
(* Modified by Theorem Labs, 2026-10 (an internal work row): Section cx below proves dr_linea_x, lib/B/W_drain_cx_x.v's
   dr_linea_stmt_x at the room texts, over any allocator relation ARx (its second half is the Section hypothesis
   LINEB_x, lib/B/W_drain_lineb_cx.v's dr_lineb_stmt_x), by the AR proof's script; Section c (dr_linea) is unchanged. *)
(* Modified by Theorem Labs, 2026-10: lib/B/W_drain_linea.v, half A of the LINEA stage of the image-B
   (fuzz_reply.asan-ubsan) walk of fuzz_reply's drain.  Proves no function (kind: segment lemma):
   dr_linea : dr_linea_stmt B MT MMAX RG (lib/B/W_drain_cx.v), DLL 0x8399c -> DLN (S q) 0x839d4 or, through the
   PROGRAM CALL send_line, DLS 0x839f4, handed to the second half dr_lineb (Section hypothesis LINEB).
   PORTED from lib/A/W_drain_linea.v (a working branch e6b5f95b285, the same proof over image A), with
   image B's code (objdump of fuzz_reply.asan-ubsan) and lib/B's interface (a working branch):
     0x8399c ld a0,208(sp); srli a3,a0,3; ld a1,240(sp); add a3,a3,a1; lb a1,0(a3); bnez a1,83db4
                                    shadow of s->skip, base from the frame slot 240(sp) (A: s5)
     0x839b4 lw a1,0(a0); bnez a1,839c8           s->skip != 0 -> the skip arm
     0x839bc sub a1,s7,s8; ld a2,184(sp); bltu a1,a2,839e8   q - p < 6001 -> the send arm
     0x839c8 lb a2,0(a3); bnez a2,83dc4; sw zero,0(a0)       s->skip = 0, DLN at 0x839d4
     0x839e8 addi a1,a1,1; mv a0,s8; jal 82854 <send_line>   -> DLS 0x839f4
   The B frame region la_fr holds 184(sp) = 6001, 208(sp) = &s->skip, 240(sp) = SHADOW_OFF; both shadow loads are
   resolved to 0 by the token layer from la_SH, as on A.  STRUCTURE also cross-checked against the old h-lane
   framework's walk of the same bytes (a working branch lib/B/Prog/drain_p_line_test.v /
   drain_p_line_send.v); nothing is copied from them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YO0c YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_place W_drain_cx W_drain_rest_model W_drain_tr W_drain_ref W_drain_lineb_cx W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_tr_peak.
(* Section cx (the ARx-generic walk, below Section c): the generic kit, its count names (ReplyCnt.v, before the kit so
   that the kit's names come last, as in W_drain_cx_x.v) and the weighted peak lemmas (ReplyTrPeakW.v, qualified) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_journal_x W_sites_x W_contract_x W_kit_x W_drain_cx_x W_drain_room_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_send_line_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---------------------------------------------------------------------------------------------------------
   The pure model of the line loop's step over one line, ported from lib/Prog/drain_b.v:2797-2989
   (scan_zero_fst, scan_zero_snd, scan_nz_app, nth_skipn_cons, firstn_nth_app, firstn_split, nth_skipn,
   nz_firstn, scan_app_z, dW_split, dW_pre_line, scan_pre, scan_line, drl_line).
   --------------------------------------------------------------------------------------------------------- *)
Lemma la_scan_zero_fst : forall sk acc d, fst (scan sk acc (0 :: d)) = fst (scan false [] d).
Proof. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma la_scan_zero_snd : forall sk acc d, snd (scan sk acc (0 :: d)) =
  if (sk || Nat.ltb LINE_LIMIT (length acc))%bool then snd (scan false [] d) else acc :: snd (scan false [] d).
Proof. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma la_scan_nz_app : forall u sk acc d, nozero u -> scan sk acc (u ++ d) = scan sk (acc ++ u) d.
Proof.
  induction u as [|b u IH]; intros sk acc d Hz.
  - rewrite app_nil_r. reflexivity.
  - pose proof (Forall_inv Hz) as Hb. pose proof (Forall_inv_tail Hz) as Hu. cbn [app].
    rewrite (scan_nz sk acc b (u ++ d) Hb), (IH sk (acc ++ [b]) d Hu), <- app_assoc. reflexivity.
Qed.

Lemma la_nth_skipn_cons : forall (l : list Z) n x, nth_error l n = Some x -> skipn n l = x :: skipn (S n) l.
Proof.
  induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
  destruct n as [|n].
  - change (Some a = Some x) in Hn. injection Hn as ->. reflexivity.
  - exact (IH n x Hn).
Qed.

Lemma la_firstn_nth_app : forall (l : list Z) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
  induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
  destruct n as [|n].
  - change (Some a = Some x) in Hn. injection Hn as ->. reflexivity.
  - change (firstn (S (S n)) (a :: l)) with (a :: firstn (S n) l). rewrite (IH n x Hn). reflexivity.
Qed.

Lemma la_firstn_split : forall P Q (l : list Z), (P <= Q)%nat -> firstn Q l = firstn P l ++ firstn (Q - P) (skipn P l).
Proof.
  induction P as [|P IH]; intros Q l HPQ.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct Q as [|Q]; [lia|]. destruct l as [|a l].
    + rewrite skipn_nil, !firstn_nil. reflexivity.
    + change (a :: firstn Q l = a :: firstn P l ++ firstn (Q - P) (skipn P l)).
      rewrite (IH Q l) by lia. reflexivity.
Qed.

Lemma la_nth_skipn : forall (l : list Z) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  induction l as [|a l IH]; intros n i.
  - rewrite skipn_nil, !nth_error_nil. reflexivity.
  - destruct n as [|n]; [reflexivity|]. change (nth_error (skipn n l) i = nth_error l (n + i)). apply IH.
Qed.

Lemma la_nz_firstn : forall (l : list Z) k, (forall i, (i < k)%nat -> nth_error l i <> Some 0) -> nozero (firstn k l).
Proof.
  unfold nozero. induction l as [|a l IH]; intros k H.
  - rewrite firstn_nil. constructor.
  - destruct k as [|k]; [change (Forall (fun b => b <> 0) (@nil Z)); constructor|].
    change (Forall (fun b => b <> 0) (a :: firstn k l)). constructor.
    + intro E. apply (H 0%nat); [lia|]. rewrite E. reflexivity.
    + apply IH. intros i Hi. exact (H (S i) ltac:(lia)).
Qed.

Lemma la_scan_app_z : forall p sk acc q,
  fst (scan sk acc (p ++ 0 :: q)) = fst (scan false [] q) /\
  snd (scan sk acc (p ++ 0 :: q)) = snd (scan sk acc (p ++ [0])) ++ snd (scan false [] q).
Proof.
  induction p as [|b p IH]; intros sk acc q.
  - cbn [app]. rewrite la_scan_zero_fst, !la_scan_zero_snd. cbn [scan snd]. split; [reflexivity|].
    destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
  - cbn [app]. destruct (Z.eq_dec b 0) as [->|Hb].
    + rewrite la_scan_zero_fst, !la_scan_zero_snd. destruct (IH false [] q) as [I1 I2].
      split; [exact I1|]. rewrite I2. destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
    + rewrite (scan_nz sk acc b (p ++ 0 :: q) Hb), (scan_nz sk acc b (p ++ [0]) Hb). apply IH.
Qed.

Lemma la_dline_len : forall s1 p q, (p <= q < length (dW s1))%nat -> length (dline s1 p q) = (q - p)%nat.
Proof. intros s1 p q H. unfold dline. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. Qed.

Lemma la_dline_nz : forall s1 p q,
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> nozero (dline s1 p q).
Proof.
  intros s1 p q H. unfold dline. apply la_nz_firstn. intros i Hi. rewrite la_nth_skipn. apply H. lia.
Qed.

Lemma la_dW_split : forall s1 p q, (p <= q)%nat -> nth_error (dW s1) q = Some 0 ->
  skipn p (dW s1) = dline s1 p q ++ 0 :: skipn (S q) (dW s1).
Proof.
  intros s1 p q HPQ HQ. unfold dline. rewrite <- (la_nth_skipn_cons _ _ _ HQ).
  rewrite <- (firstn_skipn (q - p) (skipn p (dW s1))) at 1.
  rewrite skipn_skipn. replace (q - p + p)%nat with q by lia. reflexivity.
Qed.

Lemma la_dW_pre_line : forall s1 p q, (p <= q)%nat -> nth_error (dW s1) q = Some 0 ->
  firstn (S q) (dW s1) = firstn p (dW s1) ++ dline s1 p q ++ [0].
Proof.
  intros s1 p q HPQ HQ. rewrite (la_firstn_nth_app _ _ _ HQ), (la_firstn_split p q _ HPQ), <- app_assoc.
  reflexivity.
Qed.

Lemma la_scan_pre : forall s1 p r, dbound s1 p ->
  fst (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1) ++ r)) = fst (scan (dskp s1 p) [] r) /\
  snd (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1) ++ r)) = drlp s1 p ++ snd (scan (dskp s1 p) [] r).
Proof.
  intros s1 p r (HP & HN). destruct p as [|p]; [split; reflexivity|].
  assert (HN' : nth_error (dW s1) p = Some 0).
  { destruct HN as [H0|H0]; [discriminate|]. replace p with (S p - 1)%nat by lia. exact H0. }
  unfold drlp, dskp. cbn [Nat.eqb]. rewrite (la_firstn_nth_app _ _ _ HN'), <- app_assoc. cbn [app].
  exact (la_scan_app_z (firstn p (dW s1)) (drain_b_c.ds_skip s1) [] r).
Qed.

Lemma la_scan_line : forall sk ln r, nozero ln ->
  fst (scan sk [] (ln ++ 0 :: r)) = fst (scan false [] r) /\
  snd (scan sk [] (ln ++ 0 :: r)) =
    (if (sk || Nat.ltb LINE_LIMIT (length ln))%bool then [] else [ln]) ++ snd (scan false [] r).
Proof.
  intros sk ln r Hz. rewrite (la_scan_nz_app ln sk [] _ Hz). cbn [app].
  rewrite la_scan_zero_fst, la_scan_zero_snd.
  split; [reflexivity|]. destruct (sk || Nat.ltb LINE_LIMIT (length ln))%bool; reflexivity.
Qed.

Lemma la_drl_line : forall s1 p q, dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
  drlp s1 (S q) = drlp s1 p ++ (if (dskp s1 p || Nat.ltb LINE_LIMIT (q - p))%bool then [] else [dline s1 p q]) /\
  drlq s1 p = (if (dskp s1 p || Nat.ltb LINE_LIMIT (q - p))%bool then [] else [dline s1 p q]) ++ drlq s1 (S q).
Proof.
  intros s1 p q HB HPQ HQ HNZ.
  pose proof (la_dline_nz s1 p q HNZ) as Hz. rewrite <- (la_dline_len s1 p q HPQ). split.
  - unfold drlp at 1. rewrite (la_dW_pre_line s1 p q (proj1 HPQ) HQ), (proj2 (la_scan_pre s1 p _ HB)).
    rewrite (proj2 (la_scan_line (dskp s1 p) (dline s1 p q) [] Hz)). cbn [scan snd]. rewrite app_nil_r.
    reflexivity.
  - unfold drlq at 1. rewrite (la_dW_split s1 p q (proj1 HPQ) HQ).
    rewrite (proj2 (la_scan_line (dskp s1 p) (dline s1 p q) _ Hz)). reflexivity.
Qed.

(* The skip / overlong arm's model step: the line is NOT relayed, so every line-loop value is unchanged. *)
Lemma la_drl_skip : forall s1 p q, dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
  (dskp s1 p || Nat.ltb LINE_LIMIT (q - p))%bool = true ->
  drlp s1 (S q) = drlp s1 p /\ drlq s1 p = drlq s1 (S q) /\ dskp s1 (S q) = false.
Proof.
  intros s1 p q HB HPQ HQ HNZ HK.
  destruct (la_drl_line s1 p q HB HPQ HQ HNZ) as [E1 E2]. rewrite HK in E1, E2. cbn [app] in E1, E2.
  rewrite app_nil_r in E1. split; [exact E1|]. split; [exact E2|reflexivity].
Qed.

(* The send arm's model step. *)
Lemma la_drl_send : forall s1 p q, dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
  dskp s1 p = false -> (q - p <= LINE_LIMIT)%nat ->
  drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] /\ drlq s1 p = dline s1 p q :: drlq s1 (S q).
Proof.
  intros s1 p q HB HPQ HQ HNZ HK HL.
  destruct (la_drl_line s1 p q HB HPQ HQ HNZ) as [E1 E2].
  rewrite HK, (proj2 (Nat.ltb_ge LINE_LIMIT (q - p)) HL) in E1, E2. cbn [orb app] in E1, E2.
  split; [exact E1 | exact E2].
Qed.

(* One turn of the line loop's owed trace: dlfut over `l :: rl` is send_line's trace, then dsfut over l and rl
   (drain_b_c.v lines_run's cons case, with drain_pure.v seen_tr_m for the array size). *)
Lemma la_dlfut_cons : forall (cx : dcx) s2 ab no oc H ka l rl jb o ha ks tl,
  dlfut cx s2 ab no oc H ka (l :: rl) jb o ha ks tl ->
  exists tl',
    tl = send_line_b_c.send_line_tr (dlive cx) (dxmx cx) no oc (Z.of_nat (length l) + 1) jb o ++ tl' /\
    dsfut cx s2 ab H ka l (no + (Z.of_nat (length l) + 1))
      (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) no oc (Z.of_nat (length l) + 1)) rl
      (jb + dnret (send_line_b_c.send_line_tr (dlive cx) (dxmx cx) no oc (Z.of_nat (length l) + 1) jb o))%nat
      (send_line_b_c.send_line_out (dlive cx) (dxmx cx) no oc (Z.of_nat (length l) + 1) jb o) ha ks tl'.
Proof.
intros cx s2 ab no oc H ka l rl jb o ha ks tl HL.
unfold dlfut in HL. cbn zeta in HL. cbn [drain_b_c.lines_run] in HL.
destruct HL as (tl2 & HD & HT). cbn [fst snd] in HT, HD.
rewrite !RelayRunT.nret_app in HD.
rewrite !seen_tr_m in HT, HD.
rewrite <- !app_assoc in HT.
eexists. split; [exact HT|].
unfold dsfut. cbn zeta. rewrite ?seen_tr_m.
eexists. split; [|reflexivity].
unfold dlfut. cbn zeta. exists tl2. split; [|reflexivity].
rewrite !Nat.add_assoc in HD. exact HD.
Qed.

Lemma la_dlno_eq : forall s1 p p', drlp s1 p = drlp s1 p' -> dlno s1 p = dlno s1 p'.
Proof. intros s1 p p' E. unfold dlno. rewrite E. reflexivity. Qed.
Lemma la_dlrun_eq : forall (cx : dcx) s1 p p', drlp s1 p = drlp s1 p' -> dlrun cx s1 p = dlrun cx s1 p'.
Proof. intros cx s1 p p' E. unfold dlrun. rewrite E. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------
   byte-level helpers for the relay entry's image
   --------------------------------------------------------------------------------------------------------- *)
Lemma la_nth_bzs : forall (l : list byte) j, (j < length l)%nat ->
  nth j (bzs l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
  intros l. unfold bzs. induction l as [|b l IH]; intros j Hj; [cbn [length] in Hj; lia|].
  destruct j as [|j]; [reflexivity|]. cbn [map nth]. apply IH. cbn [length] in Hj. lia.
Qed.

Lemma la_len_bzs : forall (l : list byte), length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

Lemma la_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold key_ptrs in *. cbn [map concat length]. rewrite length_app, Mem.length_le8, IH. lia.
Qed.

Lemma la_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  intros rs. induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

(* entry_bytes, split at the four bytes of s->skip: the prefix (fd, eof), the skip word, the rest. *)
Definition la_pre (e : rentry) : list byte :=
  Mem.le4 (Z_to_bv 64 (re_fd e)) ++ Mem.le4 (Z_to_bv 64 (re_eof e)).
Definition la_post (e : rentry) : list byte :=
  re_pad1 e ++ Mem.le8 (Z_to_bv 64 (re_buf e)) ++ Mem.le8 (Z_to_bv 64 (re_used e)) ++
  Mem.le8 (Z_to_bv 64 (re_cap e)) ++ Mem.le8 (Z_to_bv 64 (re_hp e)) ++
  Mem.le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e.

Lemma la_eb_split : forall e,
  entry_bytes e = la_pre e ++ Mem.le4 (Z_to_bv 64 (re_skip e)) ++ la_post e.
Proof. intros e. unfold entry_bytes, la_pre, la_post. rewrite <- !app_assoc. reflexivity. Qed.

Lemma la_pre_len : forall e, length (la_pre e) = 8%nat.
Proof. intros e. unfold la_pre. rewrite length_app, !Mem.length_le4. reflexivity. Qed.

Lemma la_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes.
  rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.

Definition la_sk0 (e : rentry) : rentry :=
  RE (re_fd e) (re_eof e) 0 (re_pad1 e) (re_buf e) (re_used e) (re_cap e) (re_hp e) (re_kh e)
     (re_pad2 e) (re_keys e) (re_U e) (re_junk e).

Lemma la_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.



Lemma la_bzs_app : forall (l1 l2 : list byte), bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.

Lemma la_bzs_zero4 : bzs (Mem.le4 (Z_to_bv 64 0)) = [0; 0; 0; 0].
Proof. vm_compute. reflexivity. Qed.

Lemma la_le_byte_0 : forall w k, YO0f.le_byte 0 w k = 0.
Proof.
  intros w k. unfold YO0f.le_byte.
  rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma la_le_byte_1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite (Z.mod_small v 256) by lia. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r.
  apply Z.mod_small. lia.
Qed.

(* The `sub a1,s7,s8` at 0x836d8 normalises to this linear form (YP0e.v aliased2 / sv_of_lin). *)
Lemma la_U_diff : forall E n m a b,
  bv_unsigned (ew E n) = a -> bv_unsigned (ew E m) = b ->
  0 <= a -> a <= b -> b < 2 ^ 63 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit (-1))) (SOff m 0)) = b - a.
Proof.
intros E n m a b Ha Hb Ha0 Hab Hb63.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite !U_SOff, U_SLit, Ha, Hb, !Z.add_0_r.
rewrite (zcanon_id a), (zcanon_id b) by (unfold M64; lia).
change (zcanon (-1)) with (M64 - 1).
replace (zcanon (a * (M64 - 1))) with (zcanon (- a)).
2:{ unfold zcanon. replace (a * (M64 - 1)) with (- a + a * M64) by lia. symmetry. apply Z_mod_plus_full. }
unfold zcanon, M64. rewrite Zplus_mod_idemp_l. replace (- a + b) with (b - a) by lia.
apply Z.mod_small. lia.
Qed.

Lemma la_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply unsigned_lit_small. exact Hz. Qed.

(* `addi a1,a1,1` after the `sub` at 0x836d8: the length of the line with its NUL. *)
Lemma la_len_bv : forall (x y : word) a b,
  bv_unsigned x = a -> bv_unsigned y = b -> 0 <= a -> a <= b -> b < 2 ^ 63 ->
  alu64 ALU_ADD (alu64 ALU_ADD (mul_div M_MUL x (Z_to_bv 64 18446744073709551615)) (Z_to_bv 64 1)) y
  = Z_to_bv 64 (b - a + 1).
Proof.
intros x y a b Hx Hy Ha Hab Hb.
rewrite bv_eq.
rewrite !alu64_add, mul64_unsigned, Hx, Hy, !la_u64 by lia.
unfold add64, mul64.
rewrite Zplus_mod_idemp_l, <- Z.add_assoc, Zplus_mod_idemp_l.
replace (a * 18446744073709551615 + (1 + b)) with (b - a + 1 + a * 2 ^ 64)
  by (change (2 ^ 64) with 18446744073709551616; ring).
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma la_nth_firstn : forall (l : list Z) k j d, (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof.
  induction l as [|a l IH]; intros k j d Hj; [rewrite firstn_nil; reflexivity|].
  destruct k as [|k]; [lia|]. destruct j as [|j]; [reflexivity|].
  cbn [firstn nth]. apply IH. lia.
Qed.

Lemma la_nth_skipn2 : forall (l : list Z) i j d, nth j (skipn i l) d = nth (i + j) l d.
Proof.
  induction l as [|a l IH]; intros i j d.
  - rewrite skipn_nil. rewrite !nth_overflow by (cbn [length]; lia). reflexivity.
  - destruct i as [|i]; [reflexivity|]. cbn [skipn Nat.add]. apply IH.
Qed.

(* A window of a byte array is a byte array. *)
Lemma la_garr8_sub : forall (W : world SEGS) m a (l : list Z) i k,
  garr8 SEGS (arm W m) a l -> (i + k <= length l)%nat ->
  garr8 SEGS (arm W m) (a + Z.of_nat i) (firstn k (skipn i l)).
Proof.
intros W m a l i k HG Hik j Hj.
rewrite firstn_length_le in Hj by (rewrite length_skipn; lia).
destruct (HG (i + j)%nat ltac:(lia)) as (Hv & Hr).
rewrite la_nth_firstn by lia. rewrite la_nth_skipn2.
split; [|exact Hr].
replace (a + Z.of_nat i + Z.of_nat j) with (a + Z.of_nat (i + j)) by lia. exact Hv.
Qed.

Lemma la_bzs_firstn : forall k (l : list byte), bzs (firstn k l) = firstn k (bzs l).
Proof.
  unfold bzs. induction k as [|k IH]; intros [|b l]; cbn [firstn map]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma la_bzs_skipn : forall i (l : list byte), bzs (skipn i l) = skipn i (bzs l).
Proof.
  unfold bzs. induction i as [|i IH]; intros [|b l]; cbn [skipn map]; try reflexivity. apply IH.
Qed.

Lemma la_nodup_app_r : forall (A : Type) (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
  intros A l1 l2. induction l1 as [|x l1 IH]; intros H; [exact H|].
  cbn [app] in H. apply NoDup_cons_iff in H. apply IH. exact (proj2 H).
Qed.

Lemma la_nodup_app_disj : forall (A : Type) (l1 l2 : list A) x,
  List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros A l1 l2 x. induction l1 as [|y l1 IH]; intros H H1 H2; [destruct H1|].
  cbn [app] in H. apply NoDup_cons_iff in H. destruct H as (Hy & H). destruct H1 as [<-|H1].
  - apply Hy. apply in_or_app. right. exact H2.
  - exact (IH H H1 H2).
Qed.

Lemma la_fs_app : forall (l1 l2 : list Z) i k, (i + k <= length l1)%nat ->
  firstn k (skipn i (l1 ++ l2)) = firstn k (skipn i l1).
Proof.
  induction l1 as [|x l1 IH]; intros l2 i k H.
  - cbn [length] in H. assert (Hk : k = 0%nat) by lia. assert (Hi : i = 0%nat) by lia.
    subst. reflexivity.
  - destruct i as [|i]; cbn [skipn app].
    + destruct k as [|k]; [reflexivity|].
      cbn [firstn]. f_equal.
      specialize (IH l2 0%nat k ltac:(cbn [length] in H; lia)). cbn [skipn] in IH. exact IH.
    + apply IH. cbn [length] in H. lia.
Qed.

Lemma la_U_srl : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.
(* the second half of LINEA: gesture_seen's classification tests, 0x839f4 .. 0x83aa4 (W_drain_lineb_cx.v) *)
Hypothesis LINEB : dr_lineb_stmt B MT MMAX RG.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* The live blocks are pairwise distinct: their extents are pairwise disjoint and non-empty, so a repeated
   block would be disjoint from itself (ported from the w4 lane's W_gesture_end.v ablocks_nodup). *)
Lemma la_ablocks_nodup : forall ly S W mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [pp nn] Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md pp nn HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  cbn [snd]. apply req_size_pos. lia. }
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
inversion Hpos as [|b0 l0 Hb Hl]; subst.
cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.

(* What a callee's journal keeps, read off ajournal_gx's inner ajournal (ported from the w4 lane's
   W_gesture_end.v ajgx_keep_high / ajgx_keep_img / fp_spares_blocks / apk_trans). *)
Lemma la_keep_high : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
gx_ok SEGS B G -> ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx
  (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.

Lemma la_keep_img : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
  (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hf).
pose proof (pa_segs_low a Hi) as HL.
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false.
rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.

Lemma la_fp_spares_blocks : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0.
pose proof (Hb b Hin). lia.
Qed.

(* The bytes of a block that is live on BOTH sides of the call and is not in the callee's footprint. *)
Lemma la_keep_blk : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> ~ inG G (p + i) -> 0 <= p + i < 2 ^ 64 ->
aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
  (HS0 & HX0 & (memS & HJi & Hag) & _) p n i H1 H2 Hi Hfp Hg Hb.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2 p n i H1 H2 Hi Hfp).
apply (aview_gagree SEGS G _ _ _ (p + i) Hag). apply inGb_false.
rewrite unsigned_lit_small by lia. exact Hg.
Qed.

(* A callee that owns no new frame leaves the caller's frame list alone. *)
Lemma la_gx_frames : forall G XO OUT STK sp0 FP ly S W mem md ly' S' W' mem' md' k,
ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W mem md [] ly' S' W' mem' md' k ->
frames S' = frames S.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md ly' S' W' mem' md' k
  (HS0 & HX0 & (memS & HJi & Hag) & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfr & _). exact Hfr.
Qed.

Lemma la_apk_trans : forall W1 (m1 : word -> option byte) W2 m2 W3 m3,
apres_kept B W1 m1 W2 m2 -> apres_kept B W2 m2 W3 m3 -> apres_kept B W1 m1 W3 m3.
Proof. intros Wa ma Wb mb Wc mc H1 H2 a Hi Ho He Hp. exact (H2 a Hi Ho He (H1 a Hi Ho He Hp)). Qed.

(* A call to a program function inside a walk, over ajournal_gx with no out-parameter (ported from the w4
   lane's W_gesture_end.v gx_callS, itself the donor's cl_callS, YC85.v:383).  The callee's contract is
   applied at its entry, from the caller's journal, and its journal is composed into the caller's
   (W_journal.v ajournal_gx_sub). *)
Lemma la_callS : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k
STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
ajournal_gx SEGS B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx SEGS B G 0 [] STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx SEGS B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + k1) /\
 ajournal_gx SEGS B G 0 [] STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros G W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 o raw ch1 K
HGx HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee.
  destruct (ajournal_gx_inner SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 memS md own lyc Sc W memc mdc k regsc STK1 o ch1 HJi);
    try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2, k1. split; [reflexivity|].
rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own).
pose proof HJ as (HS0 & _).
eapply (ajournal_gx_sub SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
intros a (r & Hr & _). destruct Hr.
Qed.

(* THE LIVENESS BRIDGE.  send_line_c.v:21-22 makes liveness depend on the length only through `len =? 0`
   (send_off cl br len = (cl <? 0) || (br =? 1) || (len =? 0); send_live = negb send_off && (dd =? 0)), and
   W_drain_cx.v:414 dctl only moves br to dd and clears ei once the stream is off.  So the controller at the
   cut sends the next line exactly when the drain as a whole is live - EXCEPT in one configuration: the
   drain's reference stream has no line at all (dr_tot (dxh cx) = 0) while the controller is otherwise live
   (cl >= 0, br <> 1, dd = 0).  There the machine's send IS live and the model's is not.  That configuration
   cannot arise at a send, because the line in hand is one of the drain's lines; dr_tot (dxh cx) <> 0 is the
   side condition below, and it is the one fact DLL does not carry. *)
Lemma la_live_bridge : forall (cx : dcx) tot ev len,
  len <> 0 -> dr_tot (dxh cx) <> 0 -> sl_live (dctl cx tot ev) len = dlive cx.
Proof.
intros cx tot ev len Hlen HT.
assert (EL : (len =? 0) = false) by (apply Z.eqb_neq; exact Hlen).
assert (ET : (dr_tot (dxh cx) =? 0) = false) by (apply Z.eqb_neq; exact HT).
unfold dlive, dr_live, sl_live, dctl, send_line_c.send_live, send_line_c.send_off.
cbn [ct_cl ct_br ct_dd].
rewrite EL, ET, !orb_false_r.
destruct (Z.eqb_spec (ct_dd (dxc cx)) 0) as [Hdd|Hdd].
- assert (Hdd1 : (ct_dd (dxc cx) =? 1) = false) by (apply Z.eqb_neq; lia).
  rewrite !andb_true_r.
  destruct (ct_cl (dxc cx) <? 0) eqn:Ecl; [reflexivity|].
  cbn [orb].
  destruct (ct_br (dxc cx) =? 1) eqn:Ebr.
  + cbn [orb]. rewrite Ebr. reflexivity.
  + destruct (tot =? 0) eqn:Etot; cbn [orb]; [rewrite Ebr | rewrite Hdd1]; reflexivity.
- rewrite !andb_false_r. reflexivity.
Qed.

(* THE CONTROLLER ADVANCES.  send_line's own controller step (W_contract.v:626 sl_ctl) applied to the
   controller after `tot` bytes is the controller after tot + len, because `off` depends on the length only
   through `len =? 0` and dctl already moved br to dd and cleared ei once the stream was off. *)
Lemma la_ctl_step : forall (cx : dcx) tot ev len, 0 <= tot -> 0 < len ->
  exists ev', sl_ctl (dctl cx tot ev) len = dctl cx (tot + len) ev'.
Proof.
intros cx tot ev len Ht Hl.
assert (EL : (len =? 0) = false) by (apply Z.eqb_neq; lia).
assert (ET : (tot + len =? 0) = false) by (apply Z.eqb_neq; lia).
unfold sl_ctl, dctl, send_line_c.send_off.
cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
rewrite EL, ET, !orb_false_r.
destruct (ct_cl (dxc cx) <? 0) eqn:Ecl; cbn [orb]; [eexists; reflexivity|].
destruct (ct_br (dxc cx) =? 1) eqn:Ebr; cbn [orb]; [eexists; rewrite Ebr; reflexivity|].
destruct (tot =? 0) eqn:Etot; cbn [orb]; [eexists; rewrite Ebr; reflexivity|].
destruct (ct_dd (dxc cx) =? 1) eqn:Edd; eexists; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The symbolic state at the line loop's head (A_dr_line, 0x836bc).

   Atoms (after the 32 registers): 32 = SA (the relay entry), 33 = s->buf + p (the line's first byte),
   34 = s->buf + q (its NUL).  Every offset in the state is a closed literal, so vm_compute never sees a
   Section variable.  Bx is the literal shadow base, which dregs_line pins into s5.  The only write window
   is the four bytes of s->skip, covered by the shadow entry over the entry's 56 bytes, so cells_safe_b
   holds.
   --------------------------------------------------------------------------------------------------------- *)
Definition la_Bx : sv := SLit SHADOW_OFF.
Definition la_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition la_SH : list shent := [ mkSHE 32 0 56 ].
Definition la_CEIL : Z := 140737479966720.

Definition la_regs : list sv :=
  sr_set (sr_set sr_atoms 24%bv (SOff 33 0)) 23%bv (SOff 34 0).
(* B keeps &s->skip at 208(sp), 6001 at 184(sp) and the shadow base at 240(sp) (A: in s5) *)
Definition la_fr : YP09.region := YP09.mkRegion (Some 2%nat) 184 248 0 0
  [ YP09.mkChunk 184 (CVal 8 (SLit 6001));
    YP09.mkChunk 208 (CVal 8 (SOff 32 8));
    YP09.mkChunk 240 (CVal 8 (SLit SHADOW_OFF)) ].
Definition la_ent (sk : Z) : YP09.region := YP09.mkRegion (Some 32%nat) 8 12 8 12
  [ YP09.mkChunk 8 (CVal 4 (SLit sk)) ].
Definition la_regions (sk : Z) : smem := [ la_fr; la_ent sk ].
Definition la_facts : facts := mkFacts
  [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF 0 la_CEIL 0); (33%nat, mkAF 0 la_CEIL 0);
    (34%nat, mkAF 0 la_CEIL 0) ] [] [].
Definition ss_la (sk : Z) : sstate := mkSS A_dr_line la_regs (la_regions sk) None la_facts.
Definition la_extra (SA BP BQ : Z) : list word := map (Z_to_bv 64) [SA; BP; BQ].

(* ---- helpers for the DLS cut: the line's bytes, and the capacity the send allocated ---- *)
Lemma la_nth_error_skipn : forall (l : list Z) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
induction l as [|x l IH]; intros n i; destruct n as [|n]; cbn [skipn Nat.add]; try reflexivity.
- destruct i; reflexivity.
- apply IH.
Qed.

Lemma la_firstn_S : forall (l : list Z) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
induction l as [|y l IH]; intros n x H; [destruct n; discriminate|].
destruct n as [|n]; cbn [firstn nth_error app] in H |- *; [injection H as <-; reflexivity|].
rewrite (IH n x H). reflexivity.
Qed.

(* Every byte send_line's growth loop ends holding was allocated by it, so the final capacity is at most the
   starting one plus what the trace allocated (W_contract.v sl_alloc_run / sl_fin_run). *)
Lemma la_fin_le_alloc : forall fuel mx no cap rem, 0 <= cap ->
sl_fin_run fuel mx no cap rem <= cap + sl_alloc_run fuel mx no cap rem.
Proof.
induction fuel as [|f IH]; intros mx no cap rem Hc; cbn [sl_fin_run sl_alloc_run]; [lia|].
destruct (rem <=? 0); [lia|].
set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
destruct (cap <? no + n) eqn:E; [apply Z.ltb_lt in E|].
- pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) ltac:(lia)). lia.
- apply IH. exact Hc.
Qed.

Lemma la_cap_le_alloc : forall c mx no cap len, 0 <= cap ->
sl_cap c mx no cap len <= cap + sl_alloc c mx no cap len.
Proof.
intros c mx no cap len Hc. rewrite sl_cap_fin. unfold sl_alloc.
destruct (sl_live c len); [apply la_fin_le_alloc; exact Hc | lia].
Qed.

(* Writability across a callee's journal: the shadow and the memory both change, so W_frame.v's
   writable_kept (one world) does not apply.  A byte that is present on the left and present on the right is
   writable on the right; a byte that is hidden or absent on the left carries its segment answer over. *)
Lemma la_wk2 : forall (Ha Hb : word -> bool) (ma mb : word -> option byte) a,
(Ha (Z_to_bv 64 a) = false -> (exists b, ma (Z_to_bv 64 a) = Some b) ->
   Hb (Z_to_bv 64 a) = false /\ (exists b, mb (Z_to_bv 64 a) = Some b)) ->
writable_at SEGS (mrestrict Ha ma) a -> writable_at SEGS (mrestrict Hb mb) a.
Proof.
intros Ha Hb ma mb a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (Ha (Z_to_bv 64 a)) eqn:EA; intros Hw.
- destruct (Hb (Z_to_bv 64 a)) eqn:EB; [exact Hw|].
  destruct (mb (Z_to_bv 64 a)); [discriminate | exact Hw].
- destruct (ma (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp eq_refl (ex_intro _ b eq_refl)) as (EB & [b2 Hb2]). rewrite EB, Hb2. discriminate.
  + destruct (Hb (Z_to_bv 64 a)) eqn:EB; [exact Hw|].
    destruct (mb (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* An element of a pairwise-disjoint list against a later one (ported from W_drain_drop.v dw_zall / dw_zpw). *)
Lemma la_zall : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; [cbn [length] in Hj; lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth].
apply IH; [exact H2 | cbn [length] in Hj; lia].
Qed.
Lemma la_zpw : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; [cbn [length] in Hj; lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply la_zall; [exact H1 | cbn [length] in Hj; lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | cbn [length] in Hj; lia].
Qed.

(* The line loop's frame and registers across two worlds (ported from W_gsfree_scratch.v gm_frame_kept /
   gm_dregs_kept). *)
Lemma la_frame_kept : forall cx (W : world SEGS) m (W' : world SEGS) m',
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W m W' m' x) ->
dr_frame RG cx W m -> dr_frame RG cx W' m'.
Proof.
intros cx W m W' m' KF HF. unfold dr_frame in *. cbv zeta in *.
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v ->
  val_mem SEGS (arm W' m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16
  & F17 & F18 & F19 & F20 & F21 & F22 & F23 & HS).
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | assumption]|]).
intros i Hi. specialize (HS i Hi). unfold DR_SAVE_OFF in HS |- *.
replace (dsp0 cx - DRAIN_FRAME + 248 + 8 * Z.of_nat i)
  with (dsp0 cx - DRAIN_FRAME + (248 + 8 * Z.of_nat i)) in * by lia.
apply V; [lia | unfold DRAIN_FRAME; lia | exact HS].
Qed.

Lemma la_dregs_kept : forall cx regs regs' (W : world SEGS) m (W' : world SEGS) m',
dregs_line RG cx regs W m ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 21 = getr regs 21 -> getr regs' 20 = getr regs 20 -> getr regs' 22 = getr regs 22 ->
getr regs' 27 = getr regs 27 -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 ->
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W m W' m' x) ->
dregs_line RG cx regs' W' m'.
Proof.
intros cx regs regs' W m W' m' HR E2 E3 E4 E21 E20 E22 E27 E8 E9 E18 KF.
destruct HR as (Hsp & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & HFR).
unfold dregs_line. unfold spZ in *. rewrite E2, E3, E4, E21, E20, E22, E27, E8, E9, E18.
do 10 (split; [assumption|]).
exact (la_frame_kept cx W m W' m' KF HFR).
Qed.

(* The relay entry's facts across two worlds (ported from W_drain_gs.v gs_aentry_okx_kept). *)
Lemma la_aentry_okx_kept : forall ly S W mem ly' S' W' mem' e,
aentry_okx B ly S W mem e ->
akept W mem W' mem' (aentry_fp e) ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) ->
aentry_okx B ly' S' W' mem' e.
Proof.
intros ly S W mem ly' S' W' mem' e
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HK HB.
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|].
  split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  unfold aentry_fp. rewrite Ec. left. reflexivity. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W mem); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
unfold aentry_fp. apply in_or_app. right. right.
apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

Lemma la_bsum_out : forall cap out, 0 <= cap -> bsum (aout_blks cap out) = cap.
Proof.
intros cap out Hc. unfold aout_blks, bsum. destruct (Z.eqb_spec cap 0); cbn [fold_right snd]; lia.
Qed.

(* a callee-saved register's side condition: read the register's number off the literal *)
Ltac la_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let z := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with z end; lia.

(* ---------------------------------------------------------------------------------------------------------
   THE SEGMENT
   --------------------------------------------------------------------------------------------------------- *)
Theorem dr_linea : dr_linea_stmt B MT MMAX RG.
Proof.
unfold dr_linea_stmt. intros cx s1 D p q W1 c1 HB HDLL HN HGS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold DLL in HDLL.
destruct HDLL as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent
  & jb & aa & oo & ha & ks & tl & Hc1 & Hregs & H26 & H23 & H24 & H19 & H25 & Hdib & Hcapp
  & Hbnd & Hpq & Hnulq & Hnoq & HDLC & Hfut).
pose proof Hregs as Hregs'.
unfold dregs_line in Hregs'.
destruct Hregs' as (Hsp & Hr3 & Hr4 & Hr21 & Hr20 & Hr22 & Hr27 & Hr8 & Hr9 & Hr18 & HFRM).
pose proof HFRM as HFRMc. unfold dr_frame in HFRMc.
destruct HFRMc as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144
  & F152 & F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & Fsav).
pose proof HGSB as HGSB0. pose proof HSM as HSM0. pose proof HSD as HSD0.
unfold IMG_TOP in HGSB0, HSM0, HSD0.
pose proof HDLC as HDLC'.
unfold DLC, LCORE in HDLC'.
destruct HDLC' as (HMEM & HLINK & HSAME & HHIST & HRST & HBUD).
pose proof HMEM as HMEM'.
unfold DMEM in HMEM'.
destruct HMEM' as (HJ & HROM & HPRES & HFRAMES & HFR2 & HGARR & HAWR & HEOK & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as HB'.
unfold DBASE in HB'.
destruct HB' as (Hafn & HBa0 & Htbl & HSAlo & HSAhi & HSA8 & HBg & HBw & HBeok & HBj4 & HBrest).
destruct Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : DRAIN_STK = 16880) by reflexivity.
assert (HFRAME : DRAIN_FRAME = 352) by reflexivity.
assert (Hdsp : dsp0 cx = spZ (dxregs cx)) by reflexivity.
assert (HSPhi : dsp0 cx <= 2 ^ 47) by lia.
(* ---- the relay entry's block and the two atoms' ranges ---- *)
assert (Htbl1 : In (dxG cx, ATABLE) (ablocks B ly1 S1)).
{ apply (Permutation_in _ (Permutation_sym HPERM)). left. reflexivity. }
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR Htbl1)
  as (HG16 & HG4096 & HGceil & HGia & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil, HGia.
assert (HSAG : dxG cx <= dxSA cx /\ dxSA cx + 56 <= dxG cx + 896)
  by (unfold ATABLE, AENT in HSAlo, HSAhi; lia).
assert (HSA1 : 4096 <= dxSA cx) by lia.
assert (HSA2 : dxSA cx + 56 <= 140737479966720) by lia.
assert (HSAc : dxSA cx + 56 <= alloc_ceiling) by lia.
assert (HSAsp : dxSA cx + 56 <= dsp0 cx - DRAIN_FRAME) by lia.
(* The relay entry's record facts stay PACKED in HEOK: unpacking it puts five disjunctions
   (re_eof, re_skip, re_cap, the buffer and the held array) in the context, and every later `lia`
   then branches over all of them (measured: 30 minutes of wall time).  Each fact below is read out
   of HEOK inside its own subproof, and only non-disjunctive facts are kept. *)
assert (Hpad1 : length (re_pad1 e1) = 4%nat) by (pose proof HEOK as (_ & _ & H & _); exact H).
assert (Hpad2 : length (re_pad2 e1) = 4%nat) by (pose proof HEOK as (_ & _ & _ & H & _); exact H).
assert (HUlen : Z.of_nat (length (re_U e1)) = re_used e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & H & _); exact H).
assert (Husedr : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & H & _); exact H).
assert (HEBL : length (entry_bytes e1) = 56%nat) by (apply la_eb_len; assumption).
assert (HUeq : bzs (re_U e1) = dW s1) by (destruct HLINK as (_ & Hu & _); exact Hu).
assert (Hdwlen : Z.of_nat (length (dW s1)) = re_used e1)
  by (rewrite <- HUeq; unfold bzs; rewrite length_map; exact HUlen).
assert (Hcappos : 0 < re_cap e1) by lia.
assert (HBUF : In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\
  Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
  garr8 SEGS (arm W1 m1) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))).
{ pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  destruct Hb as [(Hc & _ & _)|(_ & Hin & Hj & Hg)]; [lia|].
  split; [exact Hin|]. split; [exact Hj | exact Hg]. }
destruct HBUF as (Hbufin & Hjunk & Hgbuf).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbufin)
  as (HB16 & HB4096 & HBceil & HBia & HBpres & _).
assert (RQB : req_size (re_cap e1) = re_cap e1)
  by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQB in HBceil, HBia.
assert (HBP1 : 4096 <= re_buf e1 + Z.of_nat p) by lia.
assert (HBP2 : re_buf e1 + Z.of_nat p <= 140737479966720) by lia.
assert (HBQ1 : 4096 <= re_buf e1 + Z.of_nat q) by lia.
assert (HBQ2 : re_buf e1 + Z.of_nat q <= 140737479966720) by lia.
(* ---- the environment at the cut ---- *)
set (E := Eimg (Ereg regs1 (la_extra (dxSA cx) (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat q)))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32
  (Ereg regs1 (la_extra (dxSA cx) (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat q))) E)
  by (subst E; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
      change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_buf e1 + Z.of_nat p))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e1 + Z.of_nat q))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (U33 : bv_unsigned (ew E 33) = re_buf e1 + Z.of_nat p)
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_buf e1 + Z.of_nat q)
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (BV32 : base_val E (Some 32%nat) = dxSA cx)
  by (cbn [base_val]; rewrite E32; apply unsigned_lit_small; lia).
assert (BV2 : base_val E (Some 2%nat) = dsp0 cx - DRAIN_FRAME) by (cbn [base_val]; exact Usp).
(* ---- the four bytes of s->skip, read off the entry's image ---- *)
assert (HSKV : val_mem SEGS (arm W1 m1) (dxSA cx + 8) 4 (re_skip e1)).
{ intros k Hk.
  assert (Hj : ((8 + k) < length (bzs (entry_bytes e1)))%nat) by (rewrite la_len_bzs, HEBL; lia).
  destruct (HGARR (8 + k)%nat Hj) as (Hv & Hr).
  specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv.
  replace (dxSA cx + 8 + Z.of_nat k) with (dxSA cx + Z.of_nat (8 + k)) by lia.
  assert (Hnb : nth (8 + k) (bzs (entry_bytes e1)) 0 = YO0f.le_byte (re_skip e1) 4 k).
  { rewrite la_nth_bzs by (rewrite HEBL; lia). rewrite (la_eb_split e1).
    pose proof (la_pre_len e1) as HL.
    rewrite app_nth2 by lia. rewrite HL.
    replace (8 + k - 8)%nat with k by lia.
    rewrite app_nth1 by (rewrite Mem.length_le4; lia).
    pose proof HEOK as (_ & Hskip & _). destruct Hskip as [Hz|Hz]; rewrite Hz;
    (do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia). }
  rewrite Hv. f_equal. f_equal. rewrite (la_le_byte_1 _ Hr). exact Hnb. }
(* ---- the symbolic entry state, for either value of s->skip ---- *)
assert (HSOK : forall sk, re_skip e1 = sk -> 0 <= sk < 2 ^ 32 ->
  st_ok_pi SEGS VAL E (ss_la sk)
    (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_line)) m1 (seg_rom SEGS)))).
{ intros sk Hsk Hskr. rewrite restrict_mkst_fx. unfold ss_la. apply pa_entry_st_ok_full.
  - unfold la_regs.
    apply regs_ok_pin;
      [ | intros X; discriminate X
      | rewrite (den_atom0 E 34%nat (re_buf e1 + Z.of_nat q) E34) by lia; exact H23 ].
    apply regs_ok_pin;
      [ | intros X; discriminate X
      | rewrite (den_atom0 E 33%nat (re_buf e1 + Z.of_nat p) E33) by lia; exact H24 ].
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold la_regions, la_fr, la_ent.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite BV2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 184 8 (SLit 6001) 6001);
          [reflexivity | zside | zside | exact F184].
      * apply (chunk_ok_val SEGS E _ _ 208 8 (SOff 32 8) (dxSA cx + 8));
          [ apply la_den; apply (U_atom_off E 32%nat (dxSA cx) 8 E32); lia
          | cbn; lia | zside | exact F208 ].
      * apply (chunk_ok_val SEGS E _ _ 240 8 (SLit SHADOW_OFF) SHADOW_OFF);
          [reflexivity | first [zside | unfold SHADOW_OFF; cbn; lia] | zside | exact F240].
    + rewrite BV32. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (HAWR o). unfold AENT. lia.
      * repeat apply Forall_cons; try apply Forall_nil.
        apply (chunk_ok_val SEGS E _ _ 8 4 (SLit sk) sk);
          [reflexivity | cbn; lia | zside |].
        rewrite <- Hsk. exact HSKV.
  - apply pairwise_disjoint_of_extents. unfold la_regions, la_fr, la_ent, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite BV2, BV32. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [la_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E33, E34, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold la_CEIL.
    repeat match goal with |- _ /\ _ => split end; try lia.
    rewrite HFRAME, Hdsp, Zminus_mod, Hal16. vm_compute. reflexivity. }
(* ---- the shadow entry over the relay entry's 56 bytes ---- *)
assert (HAPP : forall x, dxSA cx + Z.min 0 56 <= x < dxSA cx + Z.max 0 56 ->
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
{ intros x Hx.
  assert (HMR : amem_range (dxSA cx) 56)
    by (apply (amem_range_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx) 56 HAR Htbl1);
        (rewrite ?RQT; lia)).
  unfold amem_range, kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. cbn [Z.min Z.max] in Hx. lia. }
assert (SHOK : sh_ok SEGS la_Bx la_SH E (mrestrict (w_H W1) m1)).
{ unfold sh_ok, la_SH. constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H W1) m1 E la_Bx 32%nat (dxSA cx) 56 (dxSA cx) 0 56).
  - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx) 56 HAR Htbl1);
      (rewrite ?RQT; lia).
  - unfold la_Bx. apply U_lit. unfold SHADOW_OFF. lia.
  - apply (U_atom E 32%nat (dxSA cx) E32). lia.
  - lia.
  - lia.
  - exact HAPP. }
(* ---- DLN after the skip / overlong arm's store of 0 into s->skip ---- *)
assert (DLNOF : forall (regs2 : bvmap 5 word) m2 md2,
  spZ regs2 = dsp0 cx - DRAIN_FRAME ->
  getr regs2 3 = getr (dxregs cx) 3 -> getr regs2 4 = getr (dxregs cx) 4 ->
  getr regs2 21 = w64 (dxSA cx) -> getr regs2 20 = w64 (dxSA cx + 16) ->
  getr regs2 22 = w64 (dxSA cx + 24) -> getr regs2 27 = w64 (dxSA cx + 32) ->
  getr regs2 8 = w64 (rg_s RG) -> getr regs2 9 = w64 (rg_s RG / 8) ->
  getr regs2 18 = w64 ((rg_s RG + 4) / 8) ->
  getr regs2 23 = w64 (re_buf e1 + Z.of_nat q) ->
  val_mem SEGS (arm W1 m2) (dxSA cx + 8) 4 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 8 <= x < dxSA cx + 12) ->
     aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) ->
  (forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m2 x) ->
  @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k1 ->
  (dskp s1 p || Nat.ltb LINE_LIMIT (q - p))%bool = true ->
  DLN B MT MMAX RG cx s1 D (S q) W1 (cfg_at SEGS (BASE + A_dr_next) regs2 m2 md2)).
{ intros regs2 m2 md2 Hsp2 H3' H4' H21' H20' H22' H27' H8' H9' H18' H23' HVM0 HKEEP HPR2 HJ2 HCOND.
  (* (1) the model: the line is not relayed, so every line-loop value is unchanged *)
  destruct (la_drl_skip s1 p q Hbnd Hpq Hnulq Hnoq HCOND) as (E1 & E2 & E3).
  assert (Edlno : dlno s1 (S q) = dlno s1 p) by (apply la_dlno_eq; exact E1).
  assert (Edlrun : dlrun cx s1 (S q) = dlrun cx s1 p) by (apply la_dlrun_eq; exact E1).
  assert (Edloc : dloc cx s1 (S q) = dloc cx s1 p) by (unfold dloc; rewrite Edlrun; reflexivity).
  assert (EdlH : dlH cx s1 (S q) = dlH cx s1 p) by (unfold dlH; rewrite Edlrun; reflexivity).
  assert (Edlka : dlka cx s1 (S q) = dlka cx s1 p) by (unfold dlka; rewrite Edlrun; reflexivity).
  (* (2) every byte outside the four of s->skip is kept, and writability is kept everywhere *)
  assert (KEPT : forall x, ~ (dxSA cx + 8 <= x < dxSA cx + 12) -> 0 <= x < 2 ^ 64 ->
    abyte_kept W1 m1 W1 m2 x).
  { intros x Hx Hr. split; [apply HKEEP; assumption|].
    unfold arm. apply writable_kept. intros Hp. exact (HPR2 x Hp). }
  assert (WRK : forall x, writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W1 m2) x).
  { intros x Hw. exact (writable_kept (w_H W1) m1 m2 x (fun Hp => HPR2 x Hp) Hw). }
  (* (3) s->skip's four bytes lie in the relay table's block, so they are no image byte and no byte of
         any other live block *)
  assert (HIMG : forall a, in_img SEGS a -> ~ (dxSA cx + 8 <= a < dxSA cx + 12)).
  { intros a Hi Hx.
    apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE a HAR Htbl1);
      [rewrite RQT; lia | exact Hi]. }
  assert (HIMGr : forall a, in_img SEGS a -> 0 <= a < 2 ^ 64).
  { intros a Hi. pose proof (Hsegs a Hi) as HL. unfold kLowMemEnd in HL. lia. }
  pose proof (Permutation_NoDup HPERM (la_ablocks_nodup ly1 S1 W1 m1 md1 HAR)) as NDall.
  apply NoDup_cons_iff in NDall. destruct NDall as (Hni & _).
  assert (HBLKo : forall b n a, In (b, n) (ablocks B ly1 S1) -> (b, n) <> (dxG cx, ATABLE) ->
    b <= a < b + req_size n -> ~ (dxSA cx + 8 <= a < dxSA cx + 12)).
  { intros b n a Hin Hne Ha Hx.
    pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 b n (dxG cx) ATABLE HAR Hin Htbl1 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite RQT in Hd. lia. }
  assert (HBLKr : forall b n a, In (b, n) (ablocks B ly1 S1) -> b <= a < b + req_size n ->
    0 <= a < 2 ^ 64).
  { intros b n a Hin Ha.
    destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 b n HAR Hin) as (_ & Hb4 & Hbc & _). lia. }
  (* the blocks the entry, the harness source and the controller name are blocks of S1, none of them the
     relay table's block (the permutation lists that one separately and ablocks has no duplicate) *)
  assert (HINe : forall bn, In bn (aentry_blks e1) ->
    In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)).
  { intros bn Hin. split.
    - apply (Permutation_in _ (Permutation_sym HPERM)). right. apply in_or_app. left. exact Hin.
    - intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. left. exact Hin. }
  assert (HINs : forall bn, In bn (asrc_blks h1) ->
    In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)).
  { intros bn Hin. split.
    - apply (Permutation_in _ (Permutation_sym HPERM)). right. apply in_or_app. right.
      apply in_or_app. left. exact Hin.
    - intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. right. apply in_or_app. left. exact Hin. }
  assert (HINo : forall bn, In bn (aout_blks (drain_b_c.ds_ocap
      (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) out1) ->
    In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)).
  { intros bn Hin. split.
    - apply (Permutation_in _ (Permutation_sym HPERM)). right. apply in_or_app. right.
      apply in_or_app. right. apply in_or_app. left. exact Hin.
    - intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact Hin. }
  (* (4) the three footprints are kept *)
  assert (KEPTblk : forall bn a, In bn (ablocks B ly1 S1) -> bn <> (dxG cx, ATABLE) ->
    fst bn <= a < fst bn + req_size (snd bn) -> abyte_kept W1 m1 W1 m2 a).
  { intros bn a Hin Hne Ha. destruct bn as [b n]. cbn [fst snd] in Ha.
    apply KEPT; [exact (HBLKo b n a Hin Hne Ha) | exact (HBLKr b n a Hin Ha)]. }
  assert (KEPTimg : forall a, in_img SEGS a -> abyte_kept W1 m1 W1 m2 a).
  { intros a Hi. apply KEPT; [exact (HIMG a Hi) | exact (HIMGr a Hi)]. }
  assert (KEPTe2 : forall b n a, In (b, n) (aentry_blks e1) -> b <= a < b + req_size n ->
    abyte_kept W1 m1 W1 m2 a).
  { intros b n a Hin Ha.
    exact (KEPTblk (b, n) a (proj1 (HINe _ Hin)) (proj2 (HINe _ Hin)) Ha). }
  assert (KEPTent : akept W1 m1 W1 m2 (aentry_fp e1)).
  { intros r Hr a Ha. unfold aentry_fp in Hr.
    destruct (Z.eqb_spec (re_cap e1) 0) as [Hc0|Hc0]; [lia|]. cbn [app In] in Hr.
    destruct Hr as [<- | [<- | Hr]].
    - (* the buffer *)
      unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, length_app in Ha.
      apply (KEPTe2 (re_buf e1) (re_cap e1) a); [|rewrite RQB; lia].
      unfold aentry_blks. apply in_or_app. left.
      destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. left. reflexivity.
    - (* the held array *)
      unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, la_key_ptrs_len in Ha.
      pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hheld & _).
      destruct Hheld as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
      + exfalso. rewrite Hke in Ha. cbn [length] in Ha. lia.
      + destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin)
          as (_ & _ & _ & _ & _ & _ & Hn0).
        pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (_ & Hrq).
        unfold re_nheld in Hk1.
        apply (KEPTe2 (re_hp e1) (re_kh e1) a); [|lia].
        unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
        destruct (Z.eqb_spec (re_hp e1) 0); [lia|]. left. reflexivity.
    - (* a held key *)
      apply in_map_iff in Hr. destruct Hr as (kk & Hre & Hkk). subst r.
      unfold gfp in Ha. cbn [fst snd] in Ha.
      rewrite la_len_bzs, length_app in Ha. cbn [length] in Ha.
      pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkeys).
      rewrite Forall_forall in Hkeys. destruct (Hkeys kk Hkk) as (Hin & _ & _ & Hlen).
      pose proof (req_size_pos (Z.of_nat (length (key_text kk)) + 1) ltac:(lia)) as (_ & Hrq).
      apply (KEPTe2 (key_addr kk) (Z.of_nat (length (key_text kk)) + 1) a); [|lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply in_map_iff. exists kk. split; [reflexivity | exact Hkk]. }
  (* (5) a byte of the image band lies in the layout's image range, a block byte does not (YG0d.v
     al_client_img, W_kit.v pa_img_cover), so no cell of g_s or of the controller is one of the four
     bytes the store wrote *)
  pose proof HAR as HARc. destruct HARc as (_ & HLedg & _).
  assert (HBAND : forall a, 0x10000 <= a < 0x5fc000 -> ~ (dxSA cx + 8 <= a < dxSA cx + 12)).
  { intros a Ha Hx.
    destruct (pa_img_cover ly1 S1 md1 HLedg) as (Hcv1 & Hcv2).
    destruct (al_client_img _ _ LAWS ly1 S1 W1 m1 md1 a HAR
      ltac:(left; exists (dxG cx), ATABLE; split;
            [exact Htbl1 | rewrite RQT; lia])) as (Hnz & _).
    apply Hnz. unfold in_zr. cbn [fst snd]. lia. }
  assert (KEPTband : forall a, 0x10000 <= a < 0x5fc000 -> abyte_kept W1 m1 W1 m2 a).
  { intros a Ha. apply KEPT; [exact (HBAND a Ha) | lia]. }
  (* (6) the frame lies above the allocator ceiling, so the store misses it *)
  assert (KEPTfr : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W1 m2 x).
  { intros x Hx. apply KEPT; [lia | lia]. }
  (* (7) the relay entry's image after the store: the prefix and the tail are kept, the skip word is 0 *)
  assert (HGARRn : garr8 SEGS (arm W1 m2) (dxSA cx) (bzs (entry_bytes (la_sk0 e1)))).
  { assert (Hsp0 : entry_bytes (la_sk0 e1) = la_pre e1 ++ Mem.le4 (Z_to_bv 64 0) ++ la_post e1)
      by (rewrite (la_eb_split (la_sk0 e1)); reflexivity).
    pose proof (la_eb_split e1) as Hsp1.
    assert (HPOSTL : length (la_post e1) = 44%nat).
    { pose proof HEBL as HL56. rewrite (la_eb_split e1), !length_app, la_pre_len, Mem.length_le4 in HL56.
      lia. }
    rewrite Hsp0. rewrite Hsp1 in HGARR.
    rewrite (la_bzs_app (la_pre e1)) in HGARR |- *.
    rewrite (la_bzs_app (Mem.le4 (Z_to_bv 64 (re_skip e1)))) in HGARR.
    rewrite (la_bzs_app (Mem.le4 (Z_to_bv 64 0))).
    apply garr8_app in HGARR. destruct HGARR as (HGa & HGbc).
    apply garr8_app in HGbc. destruct HGbc as (HGb & HGc).
    rewrite la_len_bzs, la_pre_len in HGb, HGc.
    rewrite la_len_bzs, Mem.length_le4 in HGc.
    apply garr8_app. split.
    - apply (akept_garr8 W1 m1 W1 m2); [|exact HGa].
      intros x Hx. rewrite la_len_bzs, la_pre_len in Hx.
      apply KEPT; [lia | lia].
    - rewrite la_len_bzs, la_pre_len. apply garr8_app. split.
      + rewrite la_bzs_zero4. intros j Hj. cbn [length] in Hj.
        assert (Hv : val_mem SEGS (arm W1 m2) (dxSA cx + Z.of_nat 8 + Z.of_nat j) 1 0).
        { intros kk Hkk. assert (Hkk0 : kk = 0%nat) by lia. subst kk.
          rewrite Z.add_0_r. specialize (HVM0 j ltac:(lia)).
          rewrite la_le_byte_0 in HVM0. rewrite la_le_byte_0.
          replace (dxSA cx + Z.of_nat 8 + Z.of_nat j) with (dxSA cx + 8 + Z.of_nat j) by lia.
          exact HVM0. }
        split; [|do 4 (destruct j as [|j]; [cbn [nth]; lia|]); lia].
        replace (nth j [0; 0; 0; 0] 0) with 0
          by (do 4 (destruct j as [|j]; [reflexivity|]); lia).
        exact Hv.
      + rewrite la_len_bzs, Mem.length_le4.
        apply (akept_garr8 W1 m1 W1 m2); [|exact HGc].
        intros x Hx. rewrite la_len_bzs in Hx.
        apply KEPT; [lia | lia]. }
  (* (8) the entry's own facts survive *)
  assert (HAWRn : awr W1 m2 (dxSA cx) AENT) by (intros o Ho; apply WRK; exact (HAWR o Ho)).
  assert (HEOKn : aentry_okx B ly1 S1 W1 m2 (la_sk0 e1)).
  { unfold aentry_okx, la_sk0 in *.
    cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk
         re_nheld] in *.
    pose proof HEOK as (Heof & _ & _ & _ & Hfd & Hcapr & _ & _ & Hbufc & Hnheld & Hheld & HND1 & HND2
      & Hkeys).
    split; [exact Heof|]. split; [left; reflexivity|].
    split; [exact Hpad1|]. split; [exact Hpad2|]. split; [exact Hfd|].
    split; [exact Hcapr|]. split; [exact HUlen|]. split; [exact Husedr|].
    split.
    { destruct Hbufc as [(Hc & _)|(Hc & Hin & Hj & Hg)]; [lia|].
      right. split; [exact Hc|]. split; [exact Hin|]. split; [exact Hj|].
      apply (akept_garr8 W1 m1 W1 m2); [|exact Hg].
      intros x Hx. apply (KEPTent (gfp (re_buf e1) (bzs (re_U e1 ++ re_junk e1)))).
      - unfold aentry_fp. apply in_or_app. left.
        destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. left. reflexivity.
      - cbn [fst snd]. exact Hx. }
    split; [exact Hnheld|].
    split.
    { destruct Hheld as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & Hg)]; [left; split; assumption|].
      right. split; [exact Hz|]. split; [exact Hin|]. split; [exact Hk1|]. split; [exact Hk2|].
      apply (akept_garr8 W1 m1 W1 m2); [|exact Hg].
      intros x Hx. apply (KEPTent (gfp (re_hp e1) (bzs (key_ptrs (re_keys e1))))).
      - unfold aentry_fp. apply in_or_app. right. left. reflexivity.
      - cbn [fst snd]. exact Hx. }
    split; [exact HND1|]. split; [exact HND2|].
    rewrite Forall_forall in Hkeys |- *. intros kk Hkk.
    destruct (Hkeys kk Hkk) as (Hin & Hg & Hnz & Hlen).
    split; [exact Hin|]. split; [|split; [exact Hnz | exact Hlen]].
    apply (akept_garr8 W1 m1 W1 m2); [|exact Hg].
    intros x Hx. apply (KEPTent (gfp (key_addr kk) (bzs (key_text kk ++ [Z_to_bv 8 0])))).
    - unfold aentry_fp. apply in_or_app. right. right.
      apply in_map_iff. exists kk. split; [reflexivity | exact Hkk].
    - cbn [fst snd]. exact Hx. }
  (* (9) the harness source and the controller's output: their footprints are image cells and blocks of
     S1 other than the relay table's *)
  assert (ABKT : forall (Wa : world SEGS) ma (Wb : world SEGS) mb (Wc : world SEGS) mc a,
    abyte_kept Wa ma Wb mb a -> abyte_kept Wb mb Wc mc a -> abyte_kept Wa ma Wc mc a).
  { intros Wa ma Wb mb Wc mc a (Hv1 & Hw1) (Hv2 & Hw2).
    split; [rewrite Hv2; exact Hv1 | intros Hh; exact (Hw2 (Hw1 Hh))]. }
  assert (HGSband : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> 0x10000 <= a < 0x5fc000)
    by (intros a Ha; unfold ASRC in *; lia).
  assert (HJ4 : (dxj cx < 4)%nat) by exact HBj4.
  assert (HHAband : forall a, dHA RG cx <= a < dHA RG cx + ASRC -> 0x10000 <= a < 0x5fc000).
  { intros a Ha. apply HGSband. unfold dHA in *. unfold ASRC in *. lia. }
  assert (KEPTlist : forall LA l lines0,
    alist_at B ly1 S1 W1 m1 LA l lines0 ->
    (forall x, LA <= x < LA + 16 -> abyte_kept W1 m1 W1 m2 x) ->
    (forall bn, In bn (alist_blks l) -> In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)) ->
    akept W1 m1 W1 m2 (alist_fp LA l)).
  { intros LA l lines0 HL HLA HB2 r Hr a Ha.
    pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
    unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
    - cbn [fst snd] in Ha. exact (HLA a Ha).
    - apply in_app_or in Hr. destruct Hr as [Hr|Hr].
      + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
        destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
        rewrite la_len_bzs, length_app, la_recs_len in Ha.
        destruct Hv as [(Hc & _)|(_ & Hin & Hj & _)]; [lia|].
        unfold hl_n in *. unfold AREC in *.
        pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
        unfold AREC in Hrq.
        apply (KEPTblk (hl_v l, AREC * hl_cap l) a);
          [ exact (proj1 (HB2 _ ltac:(unfold alist_blks; apply in_or_app; left;
              destruct (Z.eqb_spec (hl_cap l) 0); [lia|]; left; reflexivity)))
          | exact (proj2 (HB2 _ ltac:(unfold alist_blks; apply in_or_app; left;
              destruct (Z.eqb_spec (hl_cap l) 0); [lia|]; left; reflexivity)))
          | cbn [fst snd]; unfold AREC; lia ].
      + apply in_map_iff in Hr. destruct Hr as (rr & Hre & Hrr). subst r.
        unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, length_app in Ha. cbn [length] in Ha.
        rewrite Forall_forall in Hrecs. destruct (Hrecs rr Hrr) as (Hin & _).
        pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as (_ & Hrq).
        apply (KEPTblk (fst rr, Z.of_nat (length (snd rr)) + 1) a);
          [ exact (proj1 (HB2 _ ltac:(unfold alist_blks; apply in_or_app; right;
              apply in_map_iff; exists rr; split; [reflexivity | exact Hrr])))
          | exact (proj2 (HB2 _ ltac:(unfold alist_blks; apply in_or_app; right;
              apply in_map_iff; exists rr; split; [reflexivity | exact Hrr])))
          | cbn [fst snd]; lia ]. }
  assert (KEPTsrc : akept W1 m1 W1 m2 (asrc_fp (dHA RG cx) h1)).
  { pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj
      & _ & _ & Hexp & Hhld & _).
    intros r Hr a Ha. unfold asrc_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | Hr]].
    - cbn [fst snd] in Ha. apply KEPTband. exact (HHAband a Ha).
    - unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs in Ha.
      pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
      apply (KEPTblk (hs_partial h1, APARTIAL) a);
        [ exact (proj1 (HINs _ ltac:(unfold asrc_blks; left; reflexivity)))
        | exact (proj2 (HINs _ ltac:(unfold asrc_blks; left; reflexivity)))
        | cbn [fst snd]; lia ].
    - apply in_app_or in Hr. destruct Hr as [Hr|Hr].
      + apply (KEPTlist (dHA RG cx + 16) (hs_pending h1) false Hpend
          ltac:(intros x Hx; apply KEPTband; apply HHAband; unfold ASRC in *; lia)
          ltac:(intros bn Hbn; apply HINs; unfold asrc_blks; right; apply in_or_app; left; exact Hbn)
          r Hr a Ha).
      + apply in_app_or in Hr. destruct Hr as [Hr|Hr].
        * apply (KEPTlist (dHA RG cx + 64) (hs_expected h1) true Hexp
            ltac:(intros x Hx; apply KEPTband; apply HHAband; unfold ASRC in *; lia)
            ltac:(intros bn Hbn; apply HINs; unfold asrc_blks; right; apply in_or_app; right;
                  apply in_or_app; left; exact Hbn)
            r Hr a Ha).
        * apply (KEPTlist (dHA RG cx + 80) (hs_held h1) true Hhld
            ltac:(intros x Hx; apply KEPTband; apply HHAband; unfold ASRC in *; lia)
            ltac:(intros bn Hbn; apply HINs; unfold asrc_blks; right; apply in_or_app; right;
                  apply in_or_app; right; exact Hbn)
            r Hr a Ha). }
  assert (HGSLband : forall a, inG (G_DR B RG) a -> 0x10000 <= a < 0x5fc000)
    by (intros a Ha; exact (pa_img_range a (proj1 (HG a Ha)))).
  assert (KEPTout : akept W1 m1 W1 m2
    (aout_fp B RG (drain_b_c.ds_ocap
       (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) out1)).
  { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & Hblk).
    pose proof (pa_obj_img 9 ltac:(lia)) as O9. rewrite HV9 in O9.
    pose proof HSD0 as O12.
    set (OC := drain_b_c.ds_ocap
      (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) in *.
    intros r Hr a Ha. unfold aout_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
      cbn [fst snd] in Ha.
    - apply KEPTband. unfold ASRC in *. lia.
    - apply KEPTband. apply HGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (rg_nout RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTband. apply HGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (rg_capout RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTband. apply HGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (rg_out RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTband. lia.
    - apply KEPTband. apply HGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (rg_client_broken RG, 1). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTband. lia.
    - apply KEPTband. apply HGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (rg_send_eintr RG, 1). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTband. apply HGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (as_errno B, 4). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - destruct (Z.eqb_spec OC 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
      destruct Hr as [<- | []]. cbn [fst snd] in Ha.
      destruct Hblk as [(Hc & _)|(_ & _ & Hin & _)]; [exfalso; exact (Hc0 Hc)|].
      assert (Hrq : req_size OC = OC)
        by (unfold req_size; destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia | reflexivity]).
      apply (KEPTblk (out1, OC) a);
        [ exact (proj1 (HINo _ ltac:(unfold aout_blks;
            destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia|]; left; reflexivity)))
        | exact (proj2 (HINo _ ltac:(unfold aout_blks;
            destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia|]; left; reflexivity)))
        | cbn [fst snd]; rewrite Hrq; lia ]. }
  (* (10) the DLN cut at S q *)
  exists regs2, ly1, S1, m2, md2, k1, (la_sk0 e1), h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl.
  split; [reflexivity|].
  split.
  {
    unfold dregs_line, dr_frame.
    split; [exact Hsp2|]. split; [exact H3'|]. split; [exact H4'|]. split; [exact H21'|].
    split; [exact H20'|]. split; [exact H22'|]. split; [exact H27'|]. split; [exact H8'|].
    split; [exact H9'|]. split; [exact H18'|].
    repeat split;
      try (eapply akept_vm; [intros x Hx; apply KEPTfr; unfold DRAIN_FRAME in *; lia | eassumption]).
    intros i Hi. eapply akept_vm;
      [intros x Hx; apply KEPTfr; unfold DRAIN_FRAME, DR_SAVE_OFF in *; lia | exact (Fsav i Hi)]. }
  split.
  { replace (re_buf (la_sk0 e1) + Z.of_nat (S q) - 1) with (re_buf e1 + Z.of_nat q)
      by (cbn [la_sk0 re_buf]; lia).
    exact H23'. }
  split; [cbn [la_sk0 re_buf re_cap]; exact Hdib|]. split; [cbn [la_sk0 re_buf re_cap]; exact Hcapp|].
  split; [split; [lia | right; replace (S q - 1)%nat with q by lia; exact Hnulq]|].
  split; [lia|].
  split.
  { unfold DLC, LCORE. rewrite E1, E3, Edlno, Edloc, EdlH, Edlka, <- E2.
    split.
    { unfold DMEM.
      split; [exact HJ2|].
      split.
      { intros a Hrom.
        assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hin & _ & Hrr); exists sg; split; assumption).
        rewrite HKEEP; [exact (HROM a Hrom) | exact (HIMGr a Hi) | exact (HIMG a Hi)]. }
      split; [intros a Hi Ho He Hp; apply HPR2; exact (HPRES a Hi Ho He Hp)|].
      split; [exact HFRAMES|].
      split.
      {
        unfold dr_frame.
        repeat split;
        try (eapply akept_vm; [intros x Hx; apply KEPTfr; unfold DRAIN_FRAME in *; lia | eassumption]).
        intros i Hi. eapply akept_vm;
          [intros x Hx; apply KEPTfr; unfold DRAIN_FRAME, DR_SAVE_OFF in *; lia | exact (Fsav i Hi)]. }
      split; [exact HGARRn|].
      split; [exact HAWRn|].
      split; [exact HEOKn|].
      split.
      { exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 HSRC KEPTsrc
          ltac:(intros bn Hbn; exact (proj1 (HINs bn Hbn)))). }
      split.
      { intros i Hi Hne. destruct (HOTH i Hi Hne) as (f & o & V1 & V2 & Hd).
        exists f, o. split.
        { eapply akept_vm; [intros x Hx; apply KEPTband; apply HGSband; unfold ASRC in *; lia | exact V1]. }
        split; [|exact Hd].
        eapply akept_vm; [intros x Hx; apply KEPTband; apply HGSband; unfold ASRC in *; lia | exact V2]. }
      split.
      { intros x Hx Hnx. apply (ABKT (dxW cx) (dxmem cx) W1 m1 W1 m2 x); [exact (HKEPT x Hx Hnx)|].
        apply KEPTband. exact (HGSband x Hx). }
      split.
      { exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ _ _ _ out1 HOUT KEPTout
          ltac:(intros bn Hbn; exact (proj1 (HINo bn Hbn)))). }
      split; [exact HLIVE|].
      exact HPERM. }
    split.
    { unfold DLINK in HLINK |- *.
      cbn [la_sk0 re_cap re_U re_skip re_keys re_hp re_kh] in *.
      destruct HLINK as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
      split; [exact L1|]. split; [exact L2|]. split; [reflexivity|].
      split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|].
      split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact L11|]. exact L12. }
    split; [exact HSAME|].
    split; [exact HHIST|].
    split; [exact HRST | exact HBUD]. }
  rewrite Edlno, Edloc, EdlH, Edlka, <- E2. exact Hfut. }
(* ---- the two arms of the skip / overlong test ---- *)
rewrite Hc1. unfold cfg_at. change (w64 (BASE + A_dr_line)) with (Z_to_bv 64 (BASE + A_dr_line)).
pose proof HEOK as (_ & Hskip & _). destruct Hskip as [Hsk0|Hsk1].
- (* s->skip = 0: the length test decides *)
  pose proof (HSOK 0 Hsk0 ltac:(lia)) as HS.
  (* decide `bltu a1,a2,839e8` (0x839c4) on the entry state, so each arm runs exactly once: the `sub` at
     0x839bc normalises to this linear form, and the condition goes into the state's facts *)
  apply (BR W1 E (ss_la 0) _ _ _ BC_LTU
    (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SOff 34 0)) (SLit 6001) HS);
    clear HS; intros Hc HS.
  + (* taken: nul - start < 6001, so the line is relayed by send_line *)
    rewrite branch_ltu_U in Hc.
    rewrite (la_U_diff E 33%nat 34%nat _ _ U33 U34 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
    rewrite U_SLit in Hc. change (zcanon 6001) with 6001 in Hc.
    apply Z.ltb_lt in Hc.
    (* 0x8399c .. 0x839f0: the shadow and skip tests, the length, the start, and `jal send_line`; stop at send_line's entry *)
    paj_run_to_tok RUNTO HS HJ SHOK la_Bspan AF_fr_send_line.
    { unfold ss_la, la_regions, la_fr, la_ent. cbn [ss_mem].
      apply awr_ok_x_cons.
      - cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. intros a Ha. exfalso. clear - Ha. lia.
      - apply awr_ok_x_cons; [|apply awr_ok_x_nil].
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. rewrite BV32. intros a Ha.
        left. split; [|lia]. right. left. split.
        + unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
          cbn [fst snd]. unfold AENT. lia.
        + exists (dxG cx), ATABLE. split; [exact Htbl1|]. rewrite RQT. lia. }
    (* s->skip's four bytes at the call, read off the entry region (the run stored nothing; they hold 0) *)
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ev ?ssF ?msF =>
        pose proof (st_ok_pi_region_nth Ev ssF msF 1 _ HS eq_refl) as RGents
    end.
    cbn [ms_mem restrict] in RGents.
    assert (LAVMs : val_mem SEGS (arm W1 (ms_mem ms)) (dxSA cx + 8) 4 0).
    { change 4%nat with (N.to_nat 4).
      eapply (field_of_region _ _ 32%nat (dxSA cx) _ _ _ _ _ 8 4 (SLit 0) 0);
        [ exact RGents
        | rewrite E32; apply unsigned_lit_small; lia
        | left; reflexivity
        | reflexivity
        | cbn; lia
        | cbn; lia ]. }
    clear RGents.
    pmkst HS.
    prreg HS (1%bv : bv 5) S1r. prreg HS (2%bv : bv 5) S2r. prreg HS (3%bv : bv 5) S3r.
    prreg HS (4%bv : bv 5) S4r. prreg HS (8%bv : bv 5) S8r.
    prreg HS (10%bv : bv 5) S10. prreg HS (11%bv : bv 5) S11.
    prreg HS (9%bv : bv 5) S9r. prreg HS (18%bv : bv 5) S18r. prreg HS (21%bv : bv 5) S21r.
    prreg HS (22%bv : bv 5) S22r. prreg HS (23%bv : bv 5) S23r. prreg HS (24%bv : bv 5) S24r.
    prreg HS (27%bv : bv 5) S27r. prreg HS (20%bv : bv 5) S20r.
    (* The line, with its NUL: a window of the relay buffer's bytes. *)
    assert (HUL : length (re_U e1) = length (dW s1))
      by (rewrite <- HUeq; symmetry; apply la_len_bzs).
    (* the relay buffer is not g_out's block: if g_out has no block, out1 is 0 and the buffer is not;
       otherwise two live blocks with the same base are the same block, which ablocks' NoDup forbids. *)
    assert (HBUFO : re_buf e1 <> out1).
    { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & Hblk0).
      destruct Hblk0 as [(Hc0 & Ho0 & _)|(_ & _ & Hin0 & _)]; [rewrite Ho0; clear - HB4096; lia|].
      intros Heq.
      assert (DEC0 : forall x y : Z * Z, {x = y} + {x <> y}).
      { intros [x1 x2] [y1 y2]. destruct (Z.eq_dec x1 y1) as [->|N1]; [|right; congruence].
        destruct (Z.eq_dec x2 y2) as [->|N2]; [left; reflexivity | right; congruence]. }
      destruct (DEC0 (re_buf e1, re_cap e1)
        (out1, drain_b_c.ds_ocap
           (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p)))) as [Hpe|Hpe].
      - pose proof (Permutation_NoDup HPERM (la_ablocks_nodup ly1 S1 W1 m1 md1 HAR)) as NDb.
        apply NoDup_cons_iff in NDb. destruct NDb as (_ & NDb).
        refine (la_nodup_app_disj _ _ _ (re_buf e1, re_cap e1) NDb _ _).
        + unfold aentry_blks. apply in_or_app. left.
          destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. left. reflexivity.
        + apply in_or_app. right. apply in_or_app. left.
          injection Hpe as Hb2 Hc2.
          assert (HOCpos : 0 < drain_b_c.ds_ocap
            (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p)))
            by (rewrite <- Hc2; exact Hcappos).
          unfold aout_blks.
          destruct (Z.eqb_spec (drain_b_c.ds_ocap
            (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) 0) as [Hz|Hz].
          * exfalso. rewrite Hz in HOCpos. exact (Z.lt_irrefl 0 HOCpos).
          * left. rewrite Hb2, Hc2. reflexivity.
      - pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) out1 _
          HAR Hbufin Hin0 Hpe) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd.
        destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 out1 _ HAR Hin0) as (_ & _ & _ & _ & _ & _ & Hn0).
        pose proof (req_size_pos _ (proj1 Hn0)) as (Hrp & _).
        rewrite RQB in Hd. clear - Hd Heq Hcappos Hrp. lia. }
    assert (HBLL : length (firstn (q - p + 1) (skipn p (re_U e1))) = (q - p + 1)%nat).
    { rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn.
      assert (HU : length (re_U e1) = length (dW s1))
        by (rewrite <- HUeq; symmetry; apply la_len_bzs).
      clear - HU Hpq. lia. }
    assert (HADS : A_dr_send = 5808) by (vm_compute; reflexivity).
    (* la_live_bridge's side condition, dr_tot (dxh cx) <> 0: W_drain_ref.v dr_ref_line gives dref s1 <> [] at
       the line in hand, and DHIST's dPS cx = (D ++ ddata s1) ++ pstream sv with RSTART's ds_ref s1 =
       feed (dSTR cx) D put dref s1 inside the drain's reference lines (RelayModel.v lines_app, twice). *)
    assert (LASK : dskp s1 p = false).
    { destruct HLINK as (_ & _ & Hs & _). destruct (dskp s1 p); [|reflexivity].
      cbn [drain_b_c.ds_skip dvirt] in Hs. lia. }
    (* LINE_LIMIT is a unary nat literal: go through Z *)
    assert (HLL : (q - p <= LINE_LIMIT)%nat).
    { apply Nat2Z.inj_le. rewrite Nat2Z.inj_sub by (clear - Hpq; lia).
      assert (LALLZ : Z.of_nat LINE_LIMIT = 6000) by (vm_compute; reflexivity).
      rewrite LALLZ. clear - Hc. lia. }
    assert (DRTOT : dr_tot (dxh cx) <> 0).
    { pose proof HRST as (HRref & HJ1 & _).
      pose proof HHIST as (HPS & _).
      assert (HDR : dref s1 <> []) by (eapply (dr_ref_line s1 p q); eassumption).
      assert (HWN : forall l1 l2, with_nul (l1 ++ l2) = with_nul l1 ++ with_nul l2)
        by (intros l1 l2; unfold with_nul; rewrite map_app, concat_app; reflexivity).
      assert (HWP : forall l, l <> [] -> (0 < length (with_nul l))%nat).
      { intros [|x r] Hl; [contradiction|]. unfold with_nul. cbn [map concat].
        rewrite !length_app. cbn [length]. lia. }
      unfold dr_tot, dr_lines.
      change (bzs (pending_stream (dxh cx))) with (dPS cx).
      change (hs_state (dxh cx)) with (dSTR cx).
      rewrite HPS, <- app_assoc, RelayModel.lines_app, RelayModel.lines_app, <- HRref.
      change (lines (drain_b_c.ds_ref s1) (ddata s1)) with (dref s1).
      rewrite !HWN, !length_app.
      pose proof (HWP (dref s1) HDR) as HP0. clear - HP0. lia. }
    (* The run from the branch to the call stores nothing, so DMEM's memory facts carry to ms_mem ms. *)
    lazymatch goal with
    | HFx : frame_of ?Ev ?rs _ _ |- _ =>
        assert (SKEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 8 <= x < dxSA cx + 12) ->
          aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x)
        by (intros x Hx Hnx;
            apply (aview_kept_out Ev rs (w_H W1) m1 (ms_mem ms) HFx x Hx);
            intros (rr & Hin & Hr);
            unfold ss_la, la_regions, la_fr, la_ent in Hin; cbn [ss_mem add_cond In] in Hin;
            destruct Hin as [<- | [<- | []]];
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?BV32, ?BV2 in Hr; lia)
    end.
    lazymatch goal with
    | HGx : mem_grows _ _ |- _ =>
        assert (SPRES : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x)
          by (intros x Hp; exact (apresent_grows (w_H W1) m1 (ms_mem ms) x HGx Hp))
    end.
    assert (SKEPT : forall x, ~ (dxSA cx + 8 <= x < dxSA cx + 12) -> 0 <= x < 2 ^ 64 ->
      abyte_kept W1 m1 W1 (ms_mem ms) x).
    { intros x Hx Hr. split; [apply SKEEP; assumption|].
      unfold arm. apply writable_kept. intros Hp. exact (SPRES x Hp). }
    assert (SIMG : forall a, in_img SEGS a -> ~ (dxSA cx + 8 <= a < dxSA cx + 12)).
    { intros a Hi Hx.
      apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE a HAR Htbl1);
        [rewrite RQT; lia | exact Hi]. }
    assert (SIMGr : forall a, in_img SEGS a -> 0 <= a < 2 ^ 64).
    { intros a Hi. pose proof (Hsegs a Hi) as HL. unfold kLowMemEnd in HL. lia. }
    pose proof HAR as HARs. destruct HARs as (_ & HLedgS & _).
    assert (SBAND : forall a, 0x10000 <= a < 0x5fc000 -> ~ (dxSA cx + 8 <= a < dxSA cx + 12)).
    { intros a Ha Hx.
      destruct (pa_img_cover ly1 S1 md1 HLedgS) as (Hcv1 & Hcv2).
      destruct (al_client_img _ _ LAWS ly1 S1 W1 m1 md1 a HAR
        ltac:(left; exists (dxG cx), ATABLE; split;
              [exact Htbl1 | rewrite RQT; lia])) as (Hnz & _).
      apply Hnz. unfold in_zr. cbn [fst snd]. lia. }
    assert (SKBAND : forall a, 0x10000 <= a < 0x5fc000 -> abyte_kept W1 m1 W1 (ms_mem ms) a)
      by (intros a Ha; apply SKEPT; [exact (SBAND a Ha) | lia]).
    pose proof (Permutation_NoDup HPERM (la_ablocks_nodup ly1 S1 W1 m1 md1 HAR)) as NDs.
    apply NoDup_cons_iff in NDs. destruct NDs as (Hnis & _).
    assert (SBLKo : forall b n a, In (b, n) (ablocks B ly1 S1) -> (b, n) <> (dxG cx, ATABLE) ->
      b <= a < b + req_size n -> ~ (dxSA cx + 8 <= a < dxSA cx + 12)).
    { intros b n a Hin Hne Ha Hx.
      pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 b n (dxG cx) ATABLE HAR Hin Htbl1 Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite RQT in Hd. lia. }
    assert (SKBLK : forall bn a, In bn (ablocks B ly1 S1) -> bn <> (dxG cx, ATABLE) ->
      fst bn <= a < fst bn + req_size (snd bn) -> abyte_kept W1 m1 W1 (ms_mem ms) a).
    { intros bn a Hin Hne Ha. destruct bn as [b n]. cbn [fst snd] in Ha.
      apply SKEPT; [exact (SBLKo b n a Hin Hne Ha)|].
      destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 b n HAR Hin) as (_ & Hb4 & Hbc & _). lia. }
    assert (SINe : forall bn, In bn (aentry_blks e1) ->
      In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)).
    { intros bn Hin. split.
      - apply (Permutation_in _ (Permutation_sym HPERM)). right. apply in_or_app. left. exact Hin.
      - intros Heq. apply Hnis. rewrite <- Heq. apply in_or_app. left. exact Hin. }
    assert (SINo : forall bn, In bn (aout_blks (drain_b_c.ds_ocap
        (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) out1) ->
      In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)).
    { intros bn Hin. split.
      - apply (Permutation_in _ (Permutation_sym HPERM)). right. apply in_or_app. right.
        apply in_or_app. right. apply in_or_app. left. exact Hin.
      - intros Heq. apply Hnis. rewrite <- Heq. apply in_or_app. right. apply in_or_app. right.
        apply in_or_app. left. exact Hin. }
    (* rom_view and the relay buffer at the call *)
    assert (SROM : rom_view SEGS W1 (ms_mem ms)).
    { intros a Hrom.
      assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hin & _ & Hrr); exists sg; split; assumption).
      rewrite SKEEP; [exact (HROM a Hrom) | exact (SIMGr a Hi) | exact (SIMG a Hi)]. }
    assert (SGBUF : garr8 SEGS (arm W1 (ms_mem ms)) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))).
    { apply (akept_garr8 W1 m1 W1 (ms_mem ms)); [|exact Hgbuf].
      intros x Hx. rewrite la_len_bzs, length_app in Hx.
      apply (SKBLK (re_buf e1, re_cap e1) x);
        [ exact (proj1 (SINe _ ltac:(unfold aentry_blks; apply in_or_app; left;
            destruct (Z.eqb_spec (re_cap e1) 0); [lia|]; left; reflexivity)))
        | exact (proj2 (SINe _ ltac:(unfold aentry_blks; apply in_or_app; left;
            destruct (Z.eqb_spec (re_cap e1) 0); [lia|]; left; reflexivity)))
        | cbn [fst snd]; rewrite RQB; clear - Hx HUlen Hjunk Husedr; lia ]. }
    assert (SGSLband : forall a, inG (G_DR B RG) a -> 0x10000 <= a < 0x5fc000)
      by (intros a Ha; exact (pa_img_range a (proj1 (HG a Ha)))).
    assert (SKOUT : akept W1 m1 W1 (ms_mem ms)
      (aout_fp B RG (drain_b_c.ds_ocap
         (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) out1)).
    { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & Hblk).
      pose proof (pa_obj_img 9 ltac:(lia)) as O9. rewrite HV9 in O9.
      pose proof HSD0 as O12.
      set (OC := drain_b_c.ds_ocap
        (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) in *.
      intros r Hr a Ha. unfold aout_fp in Hr. cbn [In] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
        cbn [fst snd] in Ha.
      - apply SKBAND. unfold ASRC in *. lia.
      - apply SKBAND. apply SGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (rg_nout RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKBAND. apply SGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (rg_capout RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKBAND. apply SGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (rg_out RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKBAND. lia.
      - apply SKBAND. apply SGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (rg_client_broken RG, 1). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKBAND. lia.
      - apply SKBAND. apply SGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (rg_send_eintr RG, 1). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKBAND. apply SGSLband. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (as_errno B, 4). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - destruct (Z.eqb_spec OC 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
        destruct Hr as [<- | []]. cbn [fst snd] in Ha.
        destruct Hblk as [(Hcz & _)|(_ & _ & Hin & _)]; [exfalso; exact (Hc0 Hcz)|].
        assert (Hrq : req_size OC = OC)
          by (unfold req_size; destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia | reflexivity]).
        apply (SKBLK (out1, OC) a);
          [ exact (proj1 (SINo _ ltac:(unfold aout_blks;
              destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia|]; left; reflexivity)))
          | exact (proj2 (SINo _ ltac:(unfold aout_blks;
              destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia|]; left; reflexivity)))
          | cbn [fst snd]; rewrite Hrq; lia ]. }
    assert (SOUT : aout_at B RG ly1 S1 W1 (ms_mem ms)
      (dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D ++ drlp s1 p)))) ev1)
      (if dlive cx then dxO cx ++ LB1 else dxO cx) (dxmx cx)
      (if dlive cx then dlno s1 p else dxno cx)
      (drain_b_c.ds_ocap
         (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) out1).
    { exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 (ms_mem ms) _ _ _ _ _ out1 HOUT SKOUT
        ltac:(intros bn Hbn; exact (proj1 (SINo bn Hbn)))). }
    set (SLC := dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D ++ drlp s1 p)))) ev1) in *.
    set (SLO := if dlive cx then dxO cx ++ LB1 else dxO cx) in *.
    set (SLN := if dlive cx then dlno s1 p else dxno cx) in *.
    set (SLOC := drain_b_c.ds_ocap
      (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) in *.
    set (SLB := firstn (q - p + 1) (skipn p (re_U e1))) in *.
    (* The owed trace splits at this send, so dbud's three bounds give send_line's three premises. *)
    assert (HLEQ : Z.of_nat (length SLB) = Z.of_nat (length (dline s1 p q)) + 1)
      by (rewrite HBLL, (la_dline_len s1 p q Hpq); clear - Hpq; lia).
    assert (HSLIVE : sl_live SLC (Z.of_nat (length SLB)) = dlive cx).
    { unfold SLC. apply la_live_bridge; [|exact DRTOT].
      rewrite HBLL. clear - Hpq. lia. }
    assert (STRNIL : forall mx no cap len j o,
      send_line_b_c.send_line_tr false mx no cap len j o = []) by reflexivity.
    destruct (la_drl_send s1 p q Hbnd Hpq Hnulq Hnoq LASK HLL) as (ESEND1 & ESEND2).
    rewrite ESEND2 in Hfut.
    destruct (la_dlfut_cons cx (dnext (dlive cx) (dxmx cx) s1) aa (dlno s1 p) (dloc cx s1 p)
      (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) (drlq s1 (S q)) jb oo ha ks tl Hfut)
      as (tlR & HTL & HSF).
    pose proof HDLC as HDLCc. apply gs_cut_facts in HDLCc.
    destruct HDLCc as (HU0 & Hcap0 & Hmx0 & Hno0 & Hoc0 & Hka0 & Hen0 & Hec0).
    pose proof HDLC as HDLCd.
    eapply gs_cut_dnext_signs in HDLCd;
      [| exact Hmx0 | exact Hbnd | reflexivity | reflexivity | intros Hx; exact Hx].
    destruct HDLCd as (Soc & Sc & So & Sn & Se & Sec & Sk).
    assert (HSZ : tr_sizes_ok tl)
      by (exact (gs_dlfut_sizes cx (dnext (dlive cx) (dxmx cx) s1) aa (dlno s1 p) (dloc cx s1 p)
                   (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q :: drlq s1 (S q)) jb oo ha ks tl
                   Hmx0 Soc Sc So Sn Se Sec Sk Hfut)).
    pose proof HBUD as (HBmo & HBsp & HBcost & HBalloc & HBmax).
    rewrite HTL in HSZ, HBcost, HBalloc, HBmax.
    destruct (gs_tr_sizes_app _ _ HSZ) as (HSZ1 & HSZ2).
    rewrite (dr_tr_cost_app MT) in HBcost.
    rewrite dr_tr_max_app in HBmax.
    pose proof (gs_tr_cost_nonneg MT MTL _ HSZ1) as HC1.
    pose proof (gs_tr_cost_nonneg MT MTL _ HSZ2) as HC2.
    (* the PROGRAM CALL at 0x839f0: send_line (s->buf + p, q - p + 1) *)
    eapply SRr_bind.
    { eapply (la_callS (G_DR B RG) W1 (ms_regs ms) (ms_mem ms) _
        DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) []
        ly1 S1 _ _ SL_STK (ablocks_fp (aout_blks SLOC out1)) (- DRAIN_FRAME)
        (Z_to_bv 64 (BASE + A_dr_send)) []
        (fun ly2 S2 W2 regs2 mem2 md2 => exists out2,
           (* the callee's OWN journal, at G_SL: it is what says the harness source in g_s - which is in
              G_DR but not in G_SL - comes through the call unchanged *)
           (exists kk mdk, @ajournal_gx _ SK SEGS B (G_SL B RG) 0 [] SL_STK (spZ (ms_regs ms))
              (ablocks_fp (aout_blks SLOC out1)) ly1 S1 W1 (ms_mem ms) mdk [] ly2 S2 W2 mem2 md2 kk) /\
           apres_kept B W1 (ms_mem ms) W2 mem2 /\
           mo_le MT S1 S2 (sl_cost MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB))) /\
           (exists rest, Permutation (ablocks B ly1 S1) (aout_blks SLOC out1 ++ rest) /\
              Permutation (ablocks B ly2 S2)
                (aout_blks (sl_cap SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB))) out2 ++ rest)) /\
           aout_at B RG ly2 S2 W2 mem2 (sl_ctl SLC (Z.of_nat (length SLB)))
             (sl_O SLC SLO SLB) (dxmx cx) (sl_no SLC SLN (Z.of_nat (length SLB)))
             (sl_cap SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB))) out2 /\
           (sl_live SLC (Z.of_nat (length SLB)) = false -> out2 = out1))
        HG HJ).
      - unfold spZ. rewrite S2r, Usp. lia.
      - vm_compute. reflexivity.
      - unfold DRAIN_FRAME. lia.
      - unfold SL_STK, SL_FRAME, ASTACK. lia.
      - unfold DRAIN_STK, SL_STK, SL_FRAME, ASTACK, DRAIN_FRAME. lia.
      - rewrite S3r, (EE 3%nat 3%bv eq_refl), Hr3. exact Hgp.
      - rewrite S4r, (EE 4%nat 4%bv eq_refl), Hr4. exact Htp.
      - exact S1r.
      - apply (ret_ok_codeptr_v A_dr_send); rewrite HADS; [lia | reflexivity].
      - rewrite la_u64 by (rewrite HADS; lia). rewrite HADS. lia.
      - apply achain_low. unfold s0Z. rewrite S8r, (EE 8%nat 8%bv eq_refl), Hr8.
        rewrite la_u64 by (clear - HGSB0; unfold ASRC in *; lia).
        clear - HGSB0 C1. unfold ASRC in *. lia.
      - (* send_line's contract *)
        intros HPRE. eapply SRr_mono.
        { eapply (SLSPEC W1 ly1 S1 (ms_regs ms) (ms_mem ms) _ [] _ _ _ _ _ _
            (re_buf e1 + Z.of_nat p) SLB HPRE).
          - rewrite S10, E33. reflexivity.
          - rewrite S11,
              (la_len_bv (ew E 33) (ew E 34) (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat q)
                 U33 U34 ltac:(lia) ltac:(lia) ltac:(lia)).
            rewrite HBLL. f_equal. clear - Hpq. lia.
          - exact SOUT.
          - exact SROM.
          - (* the line's bytes are a window of the relay buffer's *)
            replace (bzs SLB)
              with (firstn (q - p + 1) (skipn p (bzs (re_U e1 ++ re_junk e1)))).
            2:{ unfold SLB. rewrite la_bzs_app,
                  (la_fs_app (bzs (re_U e1)) (bzs (re_junk e1)) p (q - p + 1)
                     ltac:(rewrite la_len_bzs; clear - Hpq HUL; lia)).
                rewrite la_bzs_firstn, la_bzs_skipn. reflexivity. }
            apply (la_garr8_sub W1 (ms_mem ms) (re_buf e1) _ p (q - p + 1) SGBUF).
            rewrite la_len_bzs, length_app. clear - Hpq HUL. lia.
          - clear - HBP1. lia.
          - rewrite HBLL. clear - HBQ2 HBP1 Hpq. lia.
          - (* the line sits in the relay buffer, which is not g_out's block *)
            right. left. exists (re_buf e1), (re_cap e1).
            split; [exact Hbufin|]. split; [exact HBUFO|].
            split; [clear; lia|]. rewrite RQB, HBLL. clear - Hpq HUL Hdwlen Husedr. lia.
          - (* the line is in a live block, so none of its bytes is an image byte *)
            intros a Ha HinG.
            refine (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) a HAR Hbufin _ _).
            + rewrite RQB. rewrite HBLL in Ha. clear - Ha Hpq HUL Hdwlen Husedr. lia.
            + refine (proj1 (HG a _)). unfold inG, G_DR. apply Exists_cons_tl. exact HinG.
          - (* the request bound: the send's largest request is one of the owed trace's *)
            rewrite <- (dr_sl_tr_max_c SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) jb oo), HSLIVE.
            destruct (dlive cx) eqn:HLV.
            + replace SLN with (dlno s1 p) by (unfold SLN; reflexivity).
              replace SLOC with (dloc cx s1 p) by (unfold SLOC; reflexivity).
              rewrite HLEQ. clear - HBmax. lia.
            + rewrite STRNIL. cbn [tr_max fold_right]. clear - HMMAX. lia.
          - (* the live bytes (C3): the send's requests open the trace still owed, so their peak is within that
               trace's (W_tr_peak.v sl_peak_callee) *)
            unfold sl_tr. rewrite HSLIVE.
            destruct (dlive cx) eqn:HLV.
            + replace SLN with (dlno s1 p) by (unfold SLN; reflexivity).
              replace SLOC with (dloc cx s1 p) by (unfold SLOC; reflexivity).
              rewrite HLEQ.
              exact (W_tr_peak.sl_peak_callee [] tlR (blocks_bytes S1) (blocks_bytes S1) true (dxmx cx) (dlno s1 p)
                (dloc cx s1 p) (Z.of_nat (length (dline s1 p q)) + 1) jb oo LIVE_MAX
                ltac:(unfold tr_net; cbn [fold_right]; lia) HBalloc).
            + rewrite STRNIL in HBalloc |- *. cbn [app] in HBalloc.
              pose proof (W_tr_peak.tr_peak_nonneg tlR) as HP0.
              rewrite W_tr_peak.tr_peak_nil. clear - HBalloc HP0. lia.
          - (* the meter: the send's cost is the first part of the owed trace's *)
            pose proof HB as HBb. unfold DBASE in HBb.
            destruct HBb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
              & _ & _ & _ & HMOK).
            refine (mok_station MT (dxS cx) S1 _ spent _ MTL HMOK HBmo _ _).
            + rewrite <- (dr_sl_tr_cost_c MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) jb oo), HSLIVE.
              destruct (dlive cx) eqn:HLV.
              * replace SLN with (dlno s1 p) by (unfold SLN; reflexivity).
                replace SLOC with (dloc cx s1 p) by (unfold SLOC; reflexivity).
                rewrite HLEQ. clear - HC1. lia.
              * rewrite STRNIL. cbn [tr_cost fold_right]. clear. lia.
            + rewrite <- (dr_sl_tr_cost_c MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) jb oo), HSLIVE.
              destruct (dlive cx) eqn:HLV.
              * replace SLN with (dlno s1 p) by (unfold SLN; reflexivity).
                replace SLOC with (dloc cx s1 p) by (unfold SLOC; reflexivity).
                rewrite HLEQ. clear - HBcost HC2. lia.
              * rewrite STRNIL in HBcost |- *. cbn [tr_cost fold_right] in HBcost |- *.
                clear - HBcost HC2. lia. }
        cbv beta.
        intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k2 & out2 & -> & HJ2 & HPRs & HAK2 & HMO2 & HPm2 & HO2
          & HOFF2).
        exists ly2, S2, regs2, mem2, md2, k2.
        split; [rewrite S1r, HADS; reflexivity|].
        split; [eapply ajournal_gx_G_mono;
                [intros a Ha; unfold inG, G_DR; apply Exists_cons_tl; exact Ha | exact HJ2]|].
        split; [exact HPRs|].
        exists out2. split; [exists k2; eexists; exact HJ2|].
        split; [exact HAK2|]. split; [exact HMO2|]. split; [exact HPm2|]. split; [exact HO2 | exact HOFF2].
      - (* The callee's footprint is the CURRENT g_out block, the journal's (dFP cx, W_contract.v:815) the
           ENTRY's.  A g_out block that is not one of the entry's blocks is a tmp block (YCbq.v:344).  One
           that is, is by DBASE's entry permutation the table block or a dxrest block - both impossible,
           since the current permutation lists them apart from g_out and ablocks has no duplicate - or an
           entry / source / g_out block of the entry, all of which dFP covers. *)
        intros a Ha. apply inFP_ablocks_fp_inv in Ha. destruct Ha as (pb & nb & Hin & Hpa).
        assert (HinC : In (pb, nb) (ablocks B ly1 S1)).
        { apply (Permutation_in _ (Permutation_sym HPERM)). right.
          apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (DEC : forall x y : Z * Z, {x = y} + {x <> y}).
        { intros [x1 x2] [y1 y2]. destruct (Z.eq_dec x1 y1) as [->|N1]; [|right; congruence].
          destruct (Z.eq_dec x2 y2) as [->|N2]; [left; reflexivity | right; congruence]. }
        destruct (in_dec DEC (pb, nb) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hin0].
        2:{ right. exists pb, nb. split; [exact HinC|]. split; [exact Hin0 | exact Hpa]. }
        left. split; [| exists pb, nb; split; [exact HinC | exact Hpa]].
        pose proof HB as HB0. unfold DBASE in HB0.
        destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPERM0 & _).
        apply (Permutation_in _ HPERM0) in Hin0.
        pose proof (Permutation_NoDup HPERM (la_ablocks_nodup ly1 S1 W1 m1 md1 HAR)) as ND.
        assert (DFPIN : In (pb, nb) (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++
                                     aout_blks (dxcap cx) (dxout cx)) -> inFP (dFP cx) a).
        { intros HinE. unfold dFP, dr_fp. apply (proj2 (inFP_cons _ _ _ _)). right.
          pose proof (inFP_ablocks_fp _ pb nb (a - pb) HinE ltac:(clear - Hpa; lia)) as HI.
          replace (pb + (a - pb)) with a in HI by lia. exact HI. }
        destruct Hin0 as [Heq | Hin0].
        + (* the table block: it heads the current list, so it is not also g_out's *)
          exfalso. apply NoDup_cons_iff in ND. destruct ND as (Hni & _). apply Hni. rewrite Heq.
          apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin.
        + apply in_app_or in Hin0. destruct Hin0 as [Hin0|Hin0].
          { apply DFPIN. apply in_or_app. left. exact Hin0. }
          apply in_app_or in Hin0. destruct Hin0 as [Hin0|Hin0].
          { apply DFPIN. apply in_or_app. right. apply in_or_app. left. exact Hin0. }
          apply in_app_or in Hin0. destruct Hin0 as [Hin0|Hin0].
          { apply DFPIN. apply in_or_app. right. apply in_or_app. right. exact Hin0. }
          (* a dxrest block: the current list keeps dxrest apart from g_out *)
          exfalso. apply NoDup_cons_iff in ND. destruct ND as (_ & ND).
          apply la_nodup_app_r in ND. apply la_nodup_app_r in ND.
          exact (la_nodup_app_disj _ _ _ _ ND Hin Hin0). }
    (* back in drain after the send: build DLS and hand it to LINEB *)
    intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & k3 & Hc3 & HJ3 & HJc3 & HPR3 &
      out3 & HJSL0 & HAPK3 & HMO3 & HPRM3 & HO3 & HOFF3).
    destruct HJSL0 as (kSL & mdSL & HJSL).
    destruct HPRM3 as (rest3 & HPa3 & HPb3).
    apply (LINEB cx s1 D p q W3 c3 HB); [| exact HN | exact HGS].
    (* (1) the model: the line's bytes, with their NUL, are the send's argument (s->skip is 0: LASK) *)
    assert (HBSL : bzs SLB = dline s1 p q ++ [0]).
    { unfold SLB, dline. rewrite la_bzs_firstn, la_bzs_skipn, HUeq.
      replace (q - p + 1)%nat with (S (q - p)) by lia.
      apply la_firstn_S. rewrite la_nth_error_skipn.
      replace (p + (q - p))%nat with q by lia. exact Hnulq. }
    (* (2) the run from the branch to the call stored nothing: every byte is kept, s->skip's word too *)
    assert (SKALL : forall x, 0 <= x < 2 ^ 64 -> abyte_kept W1 m1 W1 (ms_mem ms) x).
    { intros x Hx.
      destruct (Z.ltb_spec x (dxSA cx + 8)); [apply SKEPT; [lia | exact Hx]|].
      destruct (Z.ltb_spec x (dxSA cx + 12)); [|apply SKEPT; [lia | exact Hx]].
      split; [|unfold arm; apply writable_kept; intros Hp; exact (SPRES x Hp)].
      set (kk := Z.to_nat (x - (dxSA cx + 8))).
      replace x with (dxSA cx + 8 + Z.of_nat kk) by (unfold kk; lia).
      pose proof LAVMs as LV. pose proof HSKV as HSK0. rewrite Hsk0 in HSK0. unfold arm in LV, HSK0.
      unfold aview. cbv beta.
      rewrite (LV kk ltac:(unfold kk; lia)), (HSK0 kk ltac:(unfold kk; lia)). reflexivity. }
    (* (3) what the call keeps: a byte off the image by its view, an image byte by apres_kept too *)
    assert (KNI : forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
      aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W1) (ms_mem ms) a ->
      abyte_kept W1 (ms_mem ms) W3 mem3 a).
    { intros a Hr Hni HV. split; [exact HV|]. unfold arm. apply la_wk2.
      intros Hh Hb. change (apresent (w_H W3) mem3 a).
      eapply apresent_transfer; [exact Hr | exact Hni | exact HV | exact (conj Hh Hb)]. }
    assert (KIM : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
      ~ (as_errno B <= a < as_errno B + 4) ->
      aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W1) (ms_mem ms) a ->
      abyte_kept W1 (ms_mem ms) W3 mem3 a).
    { intros a Hi Ho He HV. split; [exact HV|]. unfold arm. apply la_wk2.
      intros Hh Hb. exact (HAPK3 a Hi Ho He (conj Hh Hb)). }
    (* a block of S1 that is still a block of S3 and is not g_out's *)
    assert (CKB : forall bn a, In bn (ablocks B ly1 S1) -> In bn (ablocks B ly3 S3) ->
      ~ In bn (aout_blks SLOC out1) -> fst bn <= a < fst bn + req_size (snd bn) ->
      abyte_kept W1 (ms_mem ms) W3 mem3 a).
    { intros [b n] a Hin Hin3 Hno Ha. cbn [fst snd] in Ha.
      destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 b n HAR Hin) as (_ & Hb4 & Hbc & _).
      assert (Hni : ~ in_img SEGS a)
        by (intros Hi; exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 b n a HAR Hin ltac:(lia) Hi)).
      apply KNI; [lia | exact Hni|].
      replace a with (b + (a - b)) by lia.
      apply (la_keep_blk (G_DR B RG) 0 [] SL_STK (dsp0 cx + - DRAIN_FRAME)
        (ablocks_fp (aout_blks SLOC out1)) ly1 S1 W1 (ms_mem ms) _ [] ly3 S3 W3 mem3 md3 k3
        HJc3 b n (a - b) Hin Hin3 ltac:(lia)).
      - intros Hfp. apply inFP_ablocks_fp_inv in Hfp. destruct Hfp as (pb & nb & Hinb & Hpa).
        assert (Hne : (b, n) <> (pb, nb)) by (intros Heq; rewrite Heq in Hno; exact (Hno Hinb)).
        pose proof (sep_blocks SEGS B LAWS ly1 S1 W1 m1 md1 b n pb nb HAR Hin
          (proj1 (SINo (pb, nb) Hinb)) Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Ha Hpa. lia.
      - intros Hg. apply Hni. replace (b + (a - b)) with a in Hg by lia. exact (proj1 (HG a Hg)).
      - lia. }
    (* drain's own frame lies above send_line's window *)
    assert (CKF : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 (ms_mem ms) W3 mem3 x).
    { intros x Hx. apply KNI; [lia | |].
      - intros Hi. pose proof (Hsegs x Hi) as HL. unfold kLowMemEnd in HL. lia.
      - apply (la_keep_high (G_DR B RG) 0 [] SL_STK (dsp0 cx + - DRAIN_FRAME)
          (ablocks_fp (aout_blks SLOC out1)) ly1 S1 W1 (ms_mem ms) _ [] ly3 S3 W3 mem3 md3 k3 HG HJc3 x);
          lia. }
    (* the g_s band: in G_DR, but not in G_SL, so send_line's OWN journal keeps it *)
    assert (CKG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 (ms_mem ms) W3 mem3 a).
    { intros a Ha.
      assert (HgD : inG (G_DR B RG) a).
      { unfold inG, G_DR. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
      destruct (HG a HgD) as (Hi & Ho & _).
      pose proof (la_zpw _ 2 4 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
      pose proof (la_zpw _ 2 5 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
      pose proof (la_zpw _ 2 8 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
      pose proof (la_zpw _ 2 9 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
      pose proof (la_zpw _ 2 10 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
      pose proof (la_zpw _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D11.
      cbn [nth] in D4, D5, D8, D9, D10, D11. unfold zdisj in D4, D5, D8, D9, D10, D11.
      cbn [fst snd] in D4, D5, D8, D9, D10, D11.
      assert (He : ~ (as_errno B <= a < as_errno B + 4)) by (intros He; clear - D11 Ha He; lia).
      apply KIM; [exact Hi | exact Ho | exact He|].
      apply (la_keep_img (G_SL B RG) 0 [] SL_STK (spZ (ms_regs ms))
        (ablocks_fp (aout_blks SLOC out1)) ly1 S1 W1 (ms_mem ms) mdSL [] ly3 S3 W3 mem3 md3 kSL HJSL
        a Hi Ho He).
      - apply la_fp_spares_blocks. intros [b n] Hbn.
        destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 b n HAR (proj1 (SINo (b, n) Hbn))) as (_ & H4 & _).
        exact H4.
      - intros Hg. unfold inG, G_SL in Hg. rewrite !Exists_cons, Exists_nil in Hg.
        unfold in_zr in Hg. cbn [fst snd] in Hg.
        destruct Hg as [Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[]]]]]]].
        + clear - Hg Ha D4; lia.
        + clear - Hg Ha D5; lia.
        + clear - Hg Ha D8; lia.
        + clear - Hg Ha D9; lia.
        + clear - Hg Ha D10; lia.
        + clear - Hg Ha D11; lia. }
    (* (4) the composite keeps, from DLL's state through the call to the cut's *)
    assert (ABKT : forall (Wa : world SEGS) ma (Wb : world SEGS) mb (Wc : world SEGS) mc a,
      abyte_kept Wa ma Wb mb a -> abyte_kept Wb mb Wc mc a -> abyte_kept Wa ma Wc mc a).
    { intros Wa ma Wb mb Wc mc a (Hv1 & Hw1) (Hv2 & Hw2).
      split; [rewrite Hv2; exact Hv1 | intros Hh; exact (Hw2 (Hw1 Hh))]. }
    assert (KCF : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W3 mem3 x).
    { intros x Hx. apply (ABKT W1 m1 W1 (ms_mem ms)); [apply SKALL; lia | exact (CKF x Hx)]. }
    assert (KCGc : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W3 mem3 a).
    { intros a Ha. apply (ABKT W1 m1 W1 (ms_mem ms)); [apply SKALL; unfold ASRC in *; lia | exact (CKG a Ha)]. }
    (* the blocks at the cut: the call replaced g_out's block and kept the rest *)
    assert (SNOO : forall bn, In bn ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1) ->
      ~ In bn (aout_blks SLOC out1)).
    { intros bn Hin Hino.
      pose proof (Permutation_NoDup HPERM (la_ablocks_nodup ly1 S1 W1 m1 md1 HAR)) as ND.
      rewrite app_assoc in ND.
      change ((dxG cx, ATABLE) :: (aentry_blks e1 ++ asrc_blks h1) ++ aout_blks SLOC out1 ++ dxrest cx)
        with (((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1) ++ (aout_blks SLOC out1 ++ dxrest cx))
        in ND.
      exact (la_nodup_app_disj _ _ _ bn ND Hin (in_or_app _ _ _ (or_introl Hino))). }
    assert (PR3 : Permutation rest3 ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ dxrest cx)).
    { apply (Permutation_app_inv_l (aout_blks SLOC out1)).
      eapply Permutation_trans; [apply Permutation_sym; exact HPa3|].
      eapply Permutation_trans; [exact HPERM|].
      eapply Permutation_trans; [|apply Permutation_middle].
      apply perm_skip. apply Permutation_sym.
      eapply Permutation_trans; [apply Permutation_app_swap_app|].
      apply Permutation_app_head. apply Permutation_app_swap_app. }
    assert (PERM3 : Permutation (ablocks B ly3 S3)
      ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++
         aout_blks (sl_cap SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB))) out3 ++ dxrest cx)).
    { eapply Permutation_trans; [exact HPb3|].
      eapply Permutation_trans; [apply Permutation_app_head; exact PR3|].
      eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
      apply perm_skip.
      eapply Permutation_trans; [apply Permutation_app_swap_app|].
      apply Permutation_app_head. apply Permutation_app_swap_app. }
    assert (SIN13 : forall bn, In bn ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1) ->
      In bn (ablocks B ly1 S1) /\ In bn (ablocks B ly3 S3)).
    { intros bn Hin. split.
      - apply (Permutation_in _ (Permutation_sym HPERM)).
        destruct Hin as [<-|Hin]; [left; reflexivity|right].
        rewrite app_assoc. apply in_or_app. left. exact Hin.
      - apply (Permutation_in _ (Permutation_sym PERM3)).
        destruct Hin as [<-|Hin]; [left; reflexivity|right].
        rewrite app_assoc. apply in_or_app. left. exact Hin. }
    assert (KCB : forall bn a, In bn ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1) ->
      fst bn <= a < fst bn + req_size (snd bn) -> abyte_kept W1 m1 W3 mem3 a).
    { intros bn a Hin Ha. destruct (SIN13 bn Hin) as (H1 & H3).
      apply (ABKT W1 m1 W1 (ms_mem ms)); [|exact (CKB bn a H1 H3 (SNOO bn Hin) Ha)].
      apply SKALL. destruct bn as [b n].
      destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 b n HAR H1) as (_ & Hb4 & Hbc & _).
      cbn [fst snd] in Ha. lia. }
    assert (KCE : forall b n a, In (b, n) (aentry_blks e1) -> b <= a < b + req_size n ->
      abyte_kept W1 m1 W3 mem3 a).
    { intros b n a Hin Ha. apply (KCB (b, n) a); [right; apply in_or_app; left; exact Hin | exact Ha]. }
    assert (KCS : forall bn a, In bn (asrc_blks h1) -> fst bn <= a < fst bn + req_size (snd bn) ->
      abyte_kept W1 m1 W3 mem3 a).
    { intros bn a Hin Ha. apply (KCB bn a); [right; apply in_or_app; right; exact Hin | exact Ha]. }
    (* the relay entry's footprint *)
    assert (KEN : akept W1 m1 W3 mem3 (aentry_fp e1)).
    { intros r Hr a Ha. unfold aentry_fp in Hr.
      destruct (Z.eqb_spec (re_cap e1) 0) as [Hc0|Hc0]; [lia|]. cbn [app In] in Hr.
      destruct Hr as [<- | [<- | Hr]].
      - unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, length_app in Ha.
        apply (KCE (re_buf e1) (re_cap e1) a); [|rewrite RQB; lia].
        unfold aentry_blks. apply in_or_app. left.
        destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. left. reflexivity.
      - unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, la_key_ptrs_len in Ha.
        pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hheld & _).
        destruct Hheld as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
        + exfalso. rewrite Hke in Ha. cbn [length] in Ha. lia.
        + destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin)
            as (_ & _ & _ & _ & _ & _ & Hn0).
          pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (_ & Hrq).
          unfold re_nheld in Hk1.
          apply (KCE (re_hp e1) (re_kh e1) a); [|lia].
          unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
          destruct (Z.eqb_spec (re_hp e1) 0); [lia|]. left. reflexivity.
      - apply in_map_iff in Hr. destruct Hr as (kk & Hre & Hkk). subst r.
        unfold gfp in Ha. cbn [fst snd] in Ha.
        rewrite la_len_bzs, length_app in Ha. cbn [length] in Ha.
        pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkeys).
        rewrite Forall_forall in Hkeys. destruct (Hkeys kk Hkk) as (Hin & _ & _ & Hlen).
        pose proof (req_size_pos (Z.of_nat (length (key_text kk)) + 1) ltac:(lia)) as (_ & Hrq).
        apply (KCE (key_addr kk) (Z.of_nat (length (key_text kk)) + 1) a); [|lia].
        unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
        apply in_map_iff. exists kk. split; [reflexivity | exact Hkk]. }
    (* the harness source's footprint *)
    assert (KLIST : forall LA l lines0,
      alist_at B ly1 S1 W1 m1 LA l lines0 ->
      (forall x, LA <= x < LA + 16 -> abyte_kept W1 m1 W3 mem3 x) ->
      (forall bn, In bn (alist_blks l) -> In bn (asrc_blks h1)) ->
      akept W1 m1 W3 mem3 (alist_fp LA l)).
    { intros LA l lines0 HL HLA HB2 r Hr a Ha.
      pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
      unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
      - cbn [fst snd] in Ha. exact (HLA a Ha).
      - apply in_app_or in Hr. destruct Hr as [Hr|Hr].
        + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
          destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
          rewrite la_len_bzs, length_app, la_recs_len in Ha.
          destruct Hv as [(Hcz & _)|(_ & Hin & Hj & _)]; [lia|].
          unfold hl_n in *. unfold AREC in *.
          pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
          unfold AREC in Hrq.
          apply (KCS (hl_v l, AREC * hl_cap l) a);
            [ exact (HB2 _ ltac:(unfold alist_blks; apply in_or_app; left;
                destruct (Z.eqb_spec (hl_cap l) 0); [lia|]; left; reflexivity))
            | cbn [fst snd]; unfold AREC; lia ].
        + apply in_map_iff in Hr. destruct Hr as (rr & Hre & Hrr). subst r.
          unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, length_app in Ha. cbn [length] in Ha.
          rewrite Forall_forall in Hrecs. destruct (Hrecs rr Hrr) as (Hin & _).
          pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as (_ & Hrq).
          apply (KCS (fst rr, Z.of_nat (length (snd rr)) + 1) a);
            [ exact (HB2 _ ltac:(unfold alist_blks; apply in_or_app; right;
                apply in_map_iff; exists rr; split; [reflexivity | exact Hrr]))
            | cbn [fst snd]; lia ]. }
    assert (KSRC : akept W1 m1 W3 mem3 (asrc_fp (dHA RG cx) h1)).
    { pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj
        & _ & _ & Hexp & Hhld & _).
      intros r Hr a Ha. unfold asrc_fp in Hr. cbn [In] in Hr.
      destruct Hr as [<- | [<- | Hr]].
      - cbn [fst snd] in Ha. apply KCGc. unfold dHA in *. unfold ASRC in *. lia.
      - unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs in Ha.
        pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
        apply (KCS (hs_partial h1, APARTIAL) a); [left; reflexivity | cbn [fst snd]; lia].
      - apply in_app_or in Hr. destruct Hr as [Hr|Hr].
        + apply (KLIST (dHA RG cx + 16) (hs_pending h1) _ Hpend
            ltac:(intros x Hx; apply KCGc; unfold dHA in *; unfold ASRC in *; lia)
            ltac:(intros bn Hbn; right; apply in_or_app; left; exact Hbn) r Hr a Ha).
        + apply in_app_or in Hr. destruct Hr as [Hr|Hr].
          * apply (KLIST (dHA RG cx + 64) (hs_expected h1) _ Hexp
              ltac:(intros x Hx; apply KCGc; unfold dHA in *; unfold ASRC in *; lia)
              ltac:(intros bn Hbn; right; apply in_or_app; right; apply in_or_app; left; exact Hbn)
              r Hr a Ha).
          * apply (KLIST (dHA RG cx + 80) (hs_held h1) _ Hhld
              ltac:(intros x Hx; apply KCGc; unfold dHA in *; unfold ASRC in *; lia)
              ltac:(intros bn Hbn; right; apply in_or_app; right; apply in_or_app; right; exact Hbn)
              r Hr a Ha). }
    (* (5) the registers: send_line keeps the callee-saved ones *)
    assert (PRr : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr (ms_regs ms) r).
    { intros r Hr. pose proof (HPR3 (bv_unsigned r) Hr) as Er. rewrite Z_to_bv_bv_unsigned in Er. exact Er. }
    assert (DR3 : dregs_line RG cx regs3 W3 mem3).
    { apply (la_dregs_kept cx regs1 regs3 W1 m1 W3 mem3 Hregs); [| | | | | | | | | | exact KCF].
      - rewrite (PRr 2%bv ltac:(la_cs)), S2r. exact (EE 2%nat 2%bv eq_refl).
      - rewrite (PRr 3%bv ltac:(la_cs)), S3r. exact (EE 3%nat 3%bv eq_refl).
      - rewrite (PRr 4%bv ltac:(la_cs)), S4r. exact (EE 4%nat 4%bv eq_refl).
      - rewrite (PRr 21%bv ltac:(la_cs)), S21r. exact (EE 21%nat 21%bv eq_refl).
      - rewrite (PRr 20%bv ltac:(la_cs)), S20r. exact (EE 20%nat 20%bv eq_refl).
      - rewrite (PRr 22%bv ltac:(la_cs)), S22r. exact (EE 22%nat 22%bv eq_refl).
      - rewrite (PRr 27%bv ltac:(la_cs)), S27r. exact (EE 27%nat 27%bv eq_refl).
      - rewrite (PRr 8%bv ltac:(la_cs)), S8r. exact (EE 8%nat 8%bv eq_refl).
      - rewrite (PRr 9%bv ltac:(la_cs)), S9r. exact (EE 9%nat 9%bv eq_refl).
      - rewrite (PRr 18%bv ltac:(la_cs)), S18r. exact (EE 18%nat 18%bv eq_refl). }
    (* (6) the model at the cut: the send's controller, output, count, capacity and meter *)
    assert (HWN1 : with_nul (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) =
      with_nul (lines (dSTR cx) D ++ drlp s1 p) ++ (dline s1 p q ++ [0])).
    { rewrite app_assoc. unfold with_nul. rewrite map_app, concat_app. cbn [map concat].
      rewrite app_nil_r. reflexivity. }
    destruct (la_ctl_step cx (Z.of_nat (length (with_nul (lines (dSTR cx) D ++ drlp s1 p)))) ev1
      (Z.of_nat (length SLB)) ltac:(lia) ltac:(lia)) as (ev3 & Hev3).
    assert (ECTL : sl_ctl SLC (Z.of_nat (length SLB)) =
      dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])))) ev3).
    { transitivity (dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D ++ drlp s1 p))) +
        Z.of_nat (length SLB)) ev3); [exact Hev3|].
      f_equal. rewrite HWN1, length_app, length_app. cbn [length]. rewrite HLEQ. lia. }
    assert (ESLO : sl_O SLC SLO SLB = (if dlive cx then dxO cx ++ (LB1 ++ SLB) else dxO cx)).
    { unfold sl_O. rewrite HSLIVE. unfold SLO.
      destruct (dlive cx); [rewrite <- app_assoc; reflexivity | reflexivity]. }
    assert (ESNO : sl_no SLC SLN (Z.of_nat (length SLB)) =
      (if dlive cx then dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1 else dxno cx)).
    { unfold sl_no. rewrite HSLIVE. unfold SLN. destruct (dlive cx); [rewrite HLEQ; ring | reflexivity]. }
    assert (ECAP : sl_cap SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) =
      send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
        (Z.of_nat (length (dline s1 p q)) + 1)).
    { unfold sl_cap. rewrite HSLIVE, HLEQ. unfold SLN.
      replace SLOC with (dloc cx s1 p) by reflexivity.
      destruct (dlive cx); reflexivity. }
    assert (ESC : sl_cost MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) =
      tr_cost MT (send_line_b_c.send_line_tr (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
        (Z.of_nat (length (dline s1 p q)) + 1) jb oo)).
    { rewrite <- (dr_sl_tr_cost_c MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) jb oo), HSLIVE.
      destruct (dlive cx) eqn:HLV.
      - replace SLN with (dlno s1 p) by (unfold SLN; reflexivity).
        replace SLOC with (dloc cx s1 p) by (unfold SLOC; reflexivity). rewrite HLEQ. reflexivity.
      - rewrite !STRNIL. reflexivity. }
    assert (HSLOC0 : 0 <= SLOC).
    { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & Hblk).
      destruct Hblk as [(Hz & _)|(Hz & _)]; lia. }
    (* (7) DLS *)
    unfold DLS.
    exists regs3, ly3, S3, mem3, md3, (k1 + k3), e1, h1, out3, ev3, (LB1 ++ SLB),
      (spent + sl_cost MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB))).
    eexists. exists aa. eexists. exists ha, ks, tlR.
    split; [rewrite Hc3; reflexivity|].
    split; [exact DR3|].
    split; [rewrite (PRr 23%bv ltac:(la_cs)), S23r, E34; reflexivity|].
    split; [rewrite (PRr 24%bv ltac:(la_cs)), S24r, E33; reflexivity|].
    split; [exact Hdib|]. split; [exact Hcapp|].
    split; [exact Hbnd|]. split; [exact Hpq|]. split; [exact Hnulq|]. split; [exact Hnoq|].
    split; [exact LASK|]. split; [exact HLL|].
    split.
    2:{ replace (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
          with (dlno s1 p + (Z.of_nat (length (dline s1 p q)) + 1)) by ring.
        exact HSF. }
    unfold LCORE. cbv zeta.
    split.
    { unfold DMEM.
      split; [exact HJ3|].
      split; [eapply ajournal_gx_rom_view; [exact Hsegs | exact HJc3 | exact HROMO | exact SROM]|].
      split.
      { apply (la_apk_trans (dxW cx) (dxmem cx) W1 (ms_mem ms) W3 mem3); [|exact HAPK3].
        apply (la_apk_trans (dxW cx) (dxmem cx) W1 m1 W1 (ms_mem ms)); [exact HPRES|].
        intros a Hi Ho He Hp. exact (SPRES a Hp). }
      split; [rewrite (la_gx_frames _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3); exact HFRAMES|].
      split; [exact (la_frame_kept cx W1 m1 W3 mem3 KCF HFR2)|].
      split.
      { apply (akept_garr8 W1 m1 W3 mem3); [|exact HGARR].
        intros x Hx. rewrite la_len_bzs, HEBL in Hx.
        apply (KCB (dxG cx, ATABLE) x); [left; reflexivity | cbn [fst snd]; rewrite RQT; lia]. }
      split.
      { apply (akept_awr W1 m1 W3 mem3); [|exact HAWR].
        intros x Hx. apply (KCB (dxG cx, ATABLE) x);
          [left; reflexivity | cbn [fst snd]; rewrite RQT; unfold AENT in *; lia]. }
      split.
      { apply (la_aentry_okx_kept ly1 S1 W1 m1 ly3 S3 W3 mem3 e1 HEOK KEN).
        intros bn Hbn. exact (proj2 (SIN13 bn ltac:(right; apply in_or_app; left; exact Hbn))). }
      split.
      { apply (asrc_at_kept B ly1 S1 W1 m1 ly3 S3 W3 mem3 (dHA RG cx) h1 HSRC KSRC).
        intros bn Hbn. exact (proj2 (SIN13 bn ltac:(right; apply in_or_app; right; exact Hbn))). }
      split.
      { intros i Hi Hne. destruct (HOTH i Hi Hne) as (f & o & V1 & V2 & Hd).
        exists f, o. split.
        { eapply akept_vm; [intros x Hx; apply KCGc; unfold ASRC in *; lia | exact V1]. }
        split; [|exact Hd].
        eapply akept_vm; [intros x Hx; apply KCGc; unfold ASRC in *; lia | exact V2]. }
      split.
      { intros x Hx Hnx. apply (ABKT (dxW cx) (dxmem cx) W1 m1 W3 mem3 x);
          [exact (HKEPT x Hx Hnx) | exact (KCGc x Hx)]. }
      split.
      { rewrite ECTL, ESLO, ESNO, ECAP in HO3. exact HO3. }
      split.
      { intros HLf. destruct (HLIVE HLf) as (Ho1 & Hcx1). split.
        - rewrite <- Ho1. apply HOFF3. rewrite HSLIVE. exact HLf.
        - unfold dvirt. cbv zeta. cbn [drain_b_c.ds_ocap]. rewrite HLf. exact Hcx1. }
      rewrite ECAP in PERM3. exact PERM3. }
    split.
    { pose proof HLINK as HL0. unfold DLINK in HL0 |- *.
      destruct HL0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
      split; [exact L1|]. split; [exact L2|]. split; [exact Hsk0|].
      split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|].
      split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact L11|]. exact L12. }
    split; [exact HSAME|].
    split.
    { pose proof HHIST as HH0. unfold DHIST in HH0 |- *.
      destruct HH0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
      split.
      { cbn [dvirt drain_b_c.ds_no] in H6 |- *.
        rewrite HWN1, length_app, length_app. cbn [length]. lia. }
      split; [rewrite la_bzs_app, H7, HBSL, HWN1; reflexivity|].
      split; [exact H8|]. split; [exact H9|].
      split; [|exact H11].
      replace (Z.of_nat (S (length (drlq s1 (S q))))) with (Z.of_nat (length (drlq s1 p)))
        by (rewrite ESEND2; reflexivity).
      exact H10. }
    split; [exact HRST|].
    split; [|split; [|split; [|split]]].
    * exact (mo_le_trans MT MTL _ _ _ _ _ HBmo HMO3).
    * rewrite ESC. clear - HBsp HC1. lia.
    * rewrite ESC. clear - HBcost. lia.
    * (* C3: the send moves g_out's capacity from SLOC to sl_cap, exactly its requests' net change (W_tr_peak.v
         send_line_tr_net), so the peak of the rest stays in room (tr_peak_app) *)
      rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPb3), bsum_app.
      pose proof (sl_maxr_le_cap SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) HSLOC0) as (HM0 & HM1).
      rewrite la_bsum_out by lia.
      rewrite (blocks_bytes_bsum B ly1 S1), (bsum_perm _ _ HPa3), bsum_app, (la_bsum_out SLOC out1 HSLOC0)
        in HBalloc.
      rewrite (W_tr_peak.tr_peak_app _ tlR), W_tr_peak.send_line_tr_net in HBalloc.
      rewrite ECAP. replace SLOC with (dloc cx s1 p) in HBalloc by reflexivity. clear - HBalloc. lia.
    * clear - HBmax. lia.
  + (* not taken: 6001 <= nul - start, so the line is overlong and only s->skip is cleared *)
    rewrite branch_ltu_U in Hc.
    rewrite (la_U_diff E 33%nat 34%nat _ _ U33 U34 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
    rewrite U_SLit in Hc. change (zcanon 6001) with 6001 in Hc.
    apply Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK la_Bspan A_dr_next.
    { unfold ss_la, la_regions, la_fr, la_ent. cbn [ss_mem].
      apply awr_ok_x_cons.
      - cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. intros a Ha. exfalso. clear - Ha. lia.
      - apply awr_ok_x_cons; [|apply awr_ok_x_nil].
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. rewrite BV32. intros a Ha.
        left. split; [|lia]. right. left. split.
        + unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
          cbn [fst snd]. unfold AENT. lia.
        + exists (dxG cx), ATABLE. split; [exact Htbl1|]. rewrite RQT. lia. }
    lazymatch goal with
    | HFx : frame_of ?Ev ?rs _ _ |- _ =>
        assert (LAKEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 8 <= x < dxSA cx + 12) ->
          aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x)
        by (intros x Hx Hnx;
            apply (aview_kept_out Ev rs (w_H W1) m1 (ms_mem ms) HFx x Hx);
            intros (rr & Hin & Hr);
            unfold ss_la, la_regions, la_fr, la_ent in Hin; cbn [ss_mem In] in Hin;
            destruct Hin as [<- | [<- | []]];
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?BV32, ?BV2 in Hr; lia)
    end.
    lazymatch goal with
    | HGx : mem_grows _ _ |- _ =>
        assert (LAPRES : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x)
          by (intros x Hp; exact (apresent_grows (w_H W1) m1 (ms_mem ms) x HGx Hp))
    end.
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ev ?ssF ?msF =>
        pose proof (st_ok_pi_region_nth Ev ssF msF 1 _ HS eq_refl) as RGent
    end.
    cbn [ms_mem restrict] in RGent.
    assert (LAVM0 : val_mem SEGS (arm W1 (ms_mem ms)) (dxSA cx + 8) 4 0).
    { change 4%nat with (N.to_nat 4).
      eapply (field_of_region _ _ 32%nat (dxSA cx) _ _ _ _ _ 8 4 (SLit 0) 0);
        [ exact RGent
        | rewrite E32; apply unsigned_lit_small; lia
        | left; reflexivity
        | reflexivity
        | cbn; lia
        | cbn; lia ]. }
    pmkst HS.
    prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
    prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18.
    prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
    prreg HS (27%bv : bv 5) R27. prreg HS (20%bv : bv 5) R20.
    assert (LASK : dskp s1 p = false).
    { destruct HLINK as (_ & _ & Hs & _). destruct (dskp s1 p); [|reflexivity].
      cbn [drain_b_c.ds_skip dvirt] in Hs. lia. }
    assert (LALLZ : Z.of_nat LINE_LIMIT = 6000) by (vm_compute; reflexivity).
    apply HN. apply (DLNOF (ms_regs ms) (ms_mem ms) _).
    * unfold spZ. rewrite R2. exact Usp.
    * rewrite R3; first [exact Hr3 | rewrite (EE 3%nat 3%bv eq_refl); exact Hr3].
    * rewrite R4; first [exact Hr4 | rewrite (EE 4%nat 4%bv eq_refl); exact Hr4].
    * rewrite R21; first [exact Hr21 | rewrite (EE 21%nat 21%bv eq_refl); exact Hr21].
    * rewrite R20; first [exact Hr20 | rewrite (EE 20%nat 20%bv eq_refl); exact Hr20].
    * rewrite R22; first [exact Hr22 | rewrite (EE 22%nat 22%bv eq_refl); exact Hr22].
    * rewrite R27; first [exact Hr27 | rewrite (EE 27%nat 27%bv eq_refl); exact Hr27].
    * rewrite R8; first [exact Hr8 | rewrite (EE 8%nat 8%bv eq_refl); exact Hr8].
    * rewrite R9; first [exact Hr9 | rewrite (EE 9%nat 9%bv eq_refl); exact Hr9].
    * rewrite R18; first [exact Hr18 | rewrite (EE 18%nat 18%bv eq_refl); exact Hr18].
    * rewrite R23, E34. reflexivity.
    * exact LAVM0.
    * exact LAKEEP.
    * exact LAPRES.
    * exact HJ.
    * (* LINE_LIMIT is a unary nat literal: go through Z, never through nat lia *)
      rewrite LASK. cbn [orb]. apply (proj2 (Nat.ltb_lt LINE_LIMIT (q - p))).
      apply (proj2 (Nat2Z.inj_lt LINE_LIMIT (q - p))).
      rewrite LALLZ, Nat2Z.inj_sub by (clear - Hpq; lia).
      clear - Hc. lia.
- (* s->skip = 1: the skip arm *)
  pose proof (HSOK 1 Hsk1 ltac:(lia)) as HS.
  paj_run_to_tok RUNTO HS HJ SHOK la_Bspan A_dr_next.
  { unfold ss_la, la_regions, la_fr, la_ent. cbn [ss_mem].
    apply awr_ok_x_cons.
    - cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. intros a Ha. exfalso. clear - Ha. lia.
    - apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. rewrite BV32. intros a Ha.
      left. split; [|lia]. right. left. split.
      + unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      + exists (dxG cx), ATABLE. split; [exact Htbl1|]. rewrite RQT. lia. }
  (* the store left s->skip = 0; every other byte and all presence are kept *)
  lazymatch goal with
  | HFx : frame_of ?Ev ?rs _ _ |- _ =>
      assert (LAKEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 8 <= x < dxSA cx + 12) ->
        aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x)
      by (intros x Hx Hnx;
          apply (aview_kept_out Ev rs (w_H W1) m1 (ms_mem ms) HFx x Hx);
          intros (rr & Hin & Hr);
          unfold ss_la, la_regions, la_fr, la_ent in Hin; cbn [ss_mem In] in Hin;
          destruct Hin as [<- | [<- | []]];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?BV32, ?BV2 in Hr; lia)
  end.
  lazymatch goal with
  | HGx : mem_grows _ _ |- _ =>
      assert (LAPRES : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x)
        by (intros x Hp; exact (apresent_grows (w_H W1) m1 (ms_mem ms) x HGx Hp))
  end.
  (* s->skip's four bytes, read off the final state's entry region *)
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ssF ?msF =>
      pose proof (st_ok_pi_region_nth Ev ssF msF 1 _ HS eq_refl) as RGent
  end.
  cbn [ms_mem restrict] in RGent.
  assert (LAVM0 : val_mem SEGS (arm W1 (ms_mem ms)) (dxSA cx + 8) 4 0).
  { change 4%nat with (N.to_nat 4).
    eapply (field_of_region _ _ 32%nat (dxSA cx) _ _ _ _ _ 8 4 (SLit 0) 0);
      [ exact RGent
      | rewrite E32; apply unsigned_lit_small; lia
      | left; reflexivity
      | reflexivity
      | cbn; lia
      | cbn; lia ]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18.
  prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
  prreg HS (27%bv : bv 5) R27. prreg HS (20%bv : bv 5) R20.
  assert (LASK : dskp s1 p = true).
  { destruct HLINK as (_ & _ & Hs & _). destruct (dskp s1 p); [reflexivity|].
    cbn [drain_b_c.ds_skip dvirt] in Hs. lia. }
  apply HN. apply (DLNOF (ms_regs ms) (ms_mem ms) _).
  + unfold spZ. rewrite R2. exact Usp.
  + rewrite R3; first [exact Hr3 | rewrite (EE 3%nat 3%bv eq_refl); exact Hr3].
  + rewrite R4; first [exact Hr4 | rewrite (EE 4%nat 4%bv eq_refl); exact Hr4].
  + rewrite R21; first [exact Hr21 | rewrite (EE 21%nat 21%bv eq_refl); exact Hr21].
  + rewrite R20; first [exact Hr20 | rewrite (EE 20%nat 20%bv eq_refl); exact Hr20].
  + rewrite R22; first [exact Hr22 | rewrite (EE 22%nat 22%bv eq_refl); exact Hr22].
  + rewrite R27; first [exact Hr27 | rewrite (EE 27%nat 27%bv eq_refl); exact Hr27].
  + rewrite R8; first [exact Hr8 | rewrite (EE 8%nat 8%bv eq_refl); exact Hr8].
  + rewrite R9; first [exact Hr9 | rewrite (EE 9%nat 9%bv eq_refl); exact Hr9].
  + rewrite R18; first [exact Hr18 | rewrite (EE 18%nat 18%bv eq_refl); exact Hr18].
  + rewrite R23, E34. reflexivity.
  + exact LAVM0.
  + exact LAKEEP.
  + exact LAPRES.
  + exact HJ.
  + rewrite LASK. reflexivity.
Qed.

End c.

(* ---------------------------------------------------------------------------------------------------------
   THE GENERIC WALK (an internal work row): LINEA over any allocator relation ARx with its laws, at the room texts (the room
   record RP, the entry's budget kr).  Section cx is lib/A/W_drain_linea.v's Section cx header (a working branch
   806f50fb23a), in its order and names, with image B's texts (lib/B/W_drain_cx_x.v's Section c: A_OBJ 19 / 18 / 20 /
   21 / 30, IMG_TOP, HERRAL, HSD): the variables B PST ARx MT RP MMAX RG, LAWS and, after it, the generic-relation
   facts this walk reads:
     HP0  (no hidden head in any ARx state, a Theorem Labs lane's ruling: the relay table's shadow facts are W_journal_x.v's
          range_addressable_of_block_hp0_x),
     BLKN (a live block's size is non-negative: AR_laws_x's alx_blocks has no such conjunct),
     PSTR (no read-only byte is a program static: ajournal_gx_rom_view_x's premise),
     PSTG (no byte of g_s is a program static: send_line's own journal keeps g_s by its image clause);
   then W_drain_cx_x.v's hypotheses, the allocator rules in their caller-context forms at CTX_R / CTX_F / CTX_S (this
   segment calls no allocator, so neither ALLOC_TAIL nor a call-site fact HCTX_* is stated).  LINEB_x is
   lib/B/W_drain_lineb_cx.v's dr_lineb_stmt_x, the twin of Section c's LINEB.
   The AR walk above (Section c) is unchanged.  Its Definitions are cited; its lemmas are restated here with an _x
   suffix (each over ARx where it reads the relation), so no lemma's Section generalization is relied on.
   What changes against the AR proof, and nothing else:
   - the cut predicates are W_drain_cx_x.v's (the cut's ghost list Hp1 after S1; dbud_x after LCORE_x);
   - the laws are AR_laws_x's (alx_blocks without the size bound, which BLKN gives);
   - a byte of g_s or of the controller is shown off the relay table's block by its image membership (gx_ok of
     G_DR and of HGO's cells) against blk_img_x, where the AR proof read the ledger's image cover;
   - THE ROOM at the PROGRAM CALL send_line (0x839f0): the cut's dbud_x holds
       rp_RM RP S1 (Z.to_nat (tr_cost MT_rk tl) + kr) and cnt_ok_pk RP (fun P => Z.to_nat (tr_peakP P tl) + 2),
     with tl = send_line's trace ++ tlR (la_dlfut_cons).  sl_spec_x is applied at the budget
       kr' := Z.to_nat (tr_cost MT_rk tlR) + kr,
     its room premise rp_RM RP S1 (Z.to_nat (sl_cost MT_rk ..) + kr') is dbud_x's by W_drain_room_x.v gs_rm_take
     (sl_cost MT_rk is the MT_rk charge of send_line's trace, dr_sl_tr_cost_c), its count premise cnt_ok_pk RP
     sl_pk is dbud_x's (sl_pk = 2 is the + 2), and its post's rp_RM RP S3 kr' is DLS_x's room as it stands; DLS_x's
     counts are dbud_x's with the trace's first part cut off (W_drain_room_x.v gs_cnt_step): the send moves g_out's
     block from g_capout to sl_cap, exactly its requests' net count change (la_sl_tr_cnt), and tr_peakP of tl is at
     least that change plus tlR's peak.
   --------------------------------------------------------------------------------------------------------- *)
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ Exists (in_zr a) PST.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
(* the second half of LINEA over ARx: gesture_seen's classification tests, 0x839f4 .. 0x83aa4 (W_drain_lineb_cx.v) *)
Hypothesis LINEB_x : dr_lineb_stmt_x B PST ARx MT RP MMAX RG.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* la_ablocks_nodup over ARx: the live blocks' extents are pairwise disjoint (alx_sep) and non-empty (BLKN) *)
Lemma la_ablocks_nodup_x : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR.
assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [pp nn] Hin.
  pose proof (BLKN ly S Hp W mem md pp nn HAR Hin) as Hn.
  cbn [snd]. apply req_size_pos. lia. }
destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
revert Hpos Hpw. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hpw; [constructor|].
inversion Hpos as [|b0 l0 Hb Hl]; subst.
cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. constructor; [|exact (IH Hl Hpw)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.



Lemma la_fp_spares_blocks_x : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0.
pose proof (Hb b Hin). lia.
Qed.



(* Section c's la_apk_trans, la_live_bridge, la_ctl_step, la_nth_error_skipn, la_firstn_S, la_wk2, la_zall,
   la_zpw, la_frame_kept, la_dregs_kept, la_aentry_okx_kept, la_bsum_out: the same texts (none reads AR) *)
Lemma la_apk_trans_x : forall W1 (m1 : word -> option byte) W2 m2 W3 m3,
apres_kept B W1 m1 W2 m2 -> apres_kept B W2 m2 W3 m3 -> apres_kept B W1 m1 W3 m3.
Proof. intros Wa ma Wb mb Wc mc H1 H2 a Hi Ho He Hp. exact (H2 a Hi Ho He (H1 a Hi Ho He Hp)). Qed.

(* la_callS over ajournal_gx_x (the B gesture walk's gx_callS, lib/B/W_gesture_end.v, itself the donor's cl_callS,
   YC85.v:383): the callee's contract is applied at its entry (its afn_pre_x from the caller's journal), and its
   journal is composed into the caller's (W_journal_x.v ajournal_gx_sub_x). *)
Lemma la_callS_x : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k
STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G ->
@ajournal_gx_x _ SK SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  @ajournal_gx_x _ SK SEGS B PST ARx G 0 [] STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 @ajournal_gx_x _ SK SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 @ajournal_gx_x _ SK SEGS B PST ARx G 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
exact (gx_callS_x SEGS B PST ARx LAWS pa_segs_low).
Qed.

Lemma la_live_bridge_x : forall (cx : dcx) tot ev len,
  len <> 0 -> dr_tot (dxh cx) <> 0 -> sl_live (dctl cx tot ev) len = dlive cx.
Proof.
intros cx tot ev len Hlen HT.
assert (EL : (len =? 0) = false) by (apply Z.eqb_neq; exact Hlen).
assert (ET : (dr_tot (dxh cx) =? 0) = false) by (apply Z.eqb_neq; exact HT).
unfold dlive, dr_live, sl_live, dctl, send_line_c.send_live, send_line_c.send_off.
cbn [ct_cl ct_br ct_dd].
rewrite EL, ET, !orb_false_r.
destruct (Z.eqb_spec (ct_dd (dxc cx)) 0) as [Hdd|Hdd].
- assert (Hdd1 : (ct_dd (dxc cx) =? 1) = false) by (apply Z.eqb_neq; lia).
  rewrite !andb_true_r.
  destruct (ct_cl (dxc cx) <? 0) eqn:Ecl; [reflexivity|].
  cbn [orb].
  destruct (ct_br (dxc cx) =? 1) eqn:Ebr.
  + cbn [orb]. rewrite Ebr. reflexivity.
  + destruct (tot =? 0) eqn:Etot; cbn [orb]; [rewrite Ebr | rewrite Hdd1]; reflexivity.
- rewrite !andb_false_r. reflexivity.
Qed.

Lemma la_ctl_step_x : forall (cx : dcx) tot ev len, 0 <= tot -> 0 < len ->
  exists ev', sl_ctl (dctl cx tot ev) len = dctl cx (tot + len) ev'.
Proof.
intros cx tot ev len Ht Hl.
assert (EL : (len =? 0) = false) by (apply Z.eqb_neq; lia).
assert (ET : (tot + len =? 0) = false) by (apply Z.eqb_neq; lia).
unfold sl_ctl, dctl, send_line_c.send_off.
cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
rewrite EL, ET, !orb_false_r.
destruct (ct_cl (dxc cx) <? 0) eqn:Ecl; cbn [orb]; [eexists; reflexivity|].
destruct (ct_br (dxc cx) =? 1) eqn:Ebr; cbn [orb]; [eexists; rewrite Ebr; reflexivity|].
destruct (tot =? 0) eqn:Etot; cbn [orb]; [eexists; rewrite Ebr; reflexivity|].
destruct (ct_dd (dxc cx) =? 1) eqn:Edd; eexists; reflexivity.
Qed.

Lemma la_nth_error_skipn_x : forall (l : list Z) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
induction l as [|x l IH]; intros n i; destruct n as [|n]; cbn [skipn Nat.add]; try reflexivity.
- destruct i; reflexivity.
- apply IH.
Qed.

Lemma la_firstn_S_x : forall (l : list Z) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
induction l as [|y l IH]; intros n x H; [destruct n; discriminate|].
destruct n as [|n]; cbn [firstn nth_error app] in H |- *; [injection H as <-; reflexivity|].
rewrite (IH n x H). reflexivity.
Qed.

Lemma la_wk2_x : forall (Ha Hb : word -> bool) (ma mb : word -> option byte) a,
(Ha (Z_to_bv 64 a) = false -> (exists b, ma (Z_to_bv 64 a) = Some b) ->
   Hb (Z_to_bv 64 a) = false /\ (exists b, mb (Z_to_bv 64 a) = Some b)) ->
writable_at SEGS (mrestrict Ha ma) a -> writable_at SEGS (mrestrict Hb mb) a.
Proof.
intros Ha Hb ma mb a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (Ha (Z_to_bv 64 a)) eqn:EA; intros Hw.
- destruct (Hb (Z_to_bv 64 a)) eqn:EB; [exact Hw|].
  destruct (mb (Z_to_bv 64 a)); [discriminate | exact Hw].
- destruct (ma (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp eq_refl (ex_intro _ b eq_refl)) as (EB & [b2 Hb2]). rewrite EB, Hb2. discriminate.
  + destruct (Hb (Z_to_bv 64 a)) eqn:EB; [exact Hw|].
    destruct (mb (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

Lemma la_zall_x : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; [cbn [length] in Hj; lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth].
apply IH; [exact H2 | cbn [length] in Hj; lia].
Qed.

Lemma la_zpw_x : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; [cbn [length] in Hj; lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply la_zall_x; [exact H1 | cbn [length] in Hj; lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | cbn [length] in Hj; lia].
Qed.

Lemma la_frame_kept_x : forall cx (W : world SEGS) m (W' : world SEGS) m',
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W m W' m' x) ->
dr_frame RG cx W m -> dr_frame RG cx W' m'.
Proof.
intros cx W m W' m' KF HF. unfold dr_frame in *. cbv zeta in *.
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v ->
  val_mem SEGS (arm W' m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16
  & F17 & F18 & F19 & F20 & F21 & F22 & F23 & HS).
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | assumption]|]).
intros i Hi. specialize (HS i Hi). unfold DR_SAVE_OFF in HS |- *.
replace (dsp0 cx - DRAIN_FRAME + 248 + 8 * Z.of_nat i)
  with (dsp0 cx - DRAIN_FRAME + (248 + 8 * Z.of_nat i)) in * by lia.
apply V; [lia | unfold DRAIN_FRAME; lia | exact HS].
Qed.

Lemma la_dregs_kept_x : forall cx regs regs' (W : world SEGS) m (W' : world SEGS) m',
dregs_line RG cx regs W m ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 21 = getr regs 21 -> getr regs' 20 = getr regs 20 -> getr regs' 22 = getr regs 22 ->
getr regs' 27 = getr regs 27 -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 ->
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W m W' m' x) ->
dregs_line RG cx regs' W' m'.
Proof.
intros cx regs regs' W m W' m' HR E2 E3 E4 E21 E20 E22 E27 E8 E9 E18 KF.
destruct HR as (Hsp & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & HFR).
unfold dregs_line. unfold spZ in *. rewrite E2, E3, E4, E21, E20, E22, E27, E8, E9, E18.
do 10 (split; [assumption|]).
exact (la_frame_kept_x cx W m W' m' KF HFR).
Qed.

Lemma la_aentry_okx_kept_x : forall ly S W mem ly' S' W' mem' e,
aentry_okx B ly S W mem e ->
akept W mem W' mem' (aentry_fp e) ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) ->
aentry_okx B ly' S' W' mem' e.
Proof.
intros ly S W mem ly' S' W' mem' e
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HK HB.
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|].
  split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  unfold aentry_fp. rewrite Ec. left. reflexivity. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W mem); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
unfold aentry_fp. apply in_or_app. right. right.
apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

Lemma la_bsum_out_x : forall cap out, 0 <= cap -> bsum (aout_blks cap out) = cap.
Proof.
intros cap out Hc. unfold aout_blks, bsum. destruct (Z.eqb_spec cap 0); cbn [fold_right snd]; lia.
Qed.

(* a callee-saved register's side condition: read the register's number off the literal (Section c's la_cs) *)
Ltac la_cs_x := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let z := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with z end; lia.




(* ---- THE COUNT bookkeeping of the send (an internal work row, local to this walk: send_line's own trace; self-contained) ----
   la_oc P cap: the live P-count of g_out's block at capacity cap (aout_blks: no block at cap = 0).  la_sl_tr_cnt:
   send_line's requests change the live P-count by exactly la_oc P (send_line_cap ..) - la_oc P cap - the count twin
   of W_tr_peak.v send_line_tr_net (each growth replaces g_out's block; a growth from cap = 0 is a malloc, from
   cap <> 0 a realloc, and asks (no + n) * 2 > 0). *)

Definition la_oc (P : Z -> bool) (cap : Z) : Z := if cap =? 0 then 0 else zb (P cap).

Lemma la_net_cons : forall (w : Z -> Z) (X : Type) (ev : RelayRunT.rev X) (r : list (RelayRunT.rev X)),
  ReplyTrPeakW.tr_net_w w (ev :: r) =
  match ev with
  | RelayRunT.RMalloc n => w n
  | RelayRunT.RFree k _ => - w k
  | RelayRunT.RRealloc k n _ => w n - w k
  end + ReplyTrPeakW.tr_net_w w r.
Proof. reflexivity. Qed.

Lemma la_sl_run_cnt : forall (P : Z -> bool) f mx no cap rem j o, 0 <= cap ->
  ReplyTrPeakW.tr_net_w (fun n => zb (P n)) (fst (send_line_b_c.sl_run f mx no cap rem j o)) =
  la_oc P (fst (snd (send_line_b_c.sl_run f mx no cap rem j o))) - la_oc P cap.
Proof.
intros P. induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run].
- cbn [fst snd]. unfold ReplyTrPeakW.tr_net_w. cbn [fold_right]. lia.
- destruct (rem <=? 0); [cbn [fst snd]; unfold ReplyTrPeakW.tr_net_w; cbn [fold_right]; lia|].
  match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
  destruct (Z.ltb_spec cap (no + n)) as [Hl|Hl]; cbv beta iota; [|apply IH; exact Hc].
  cbn [fst snd]. rewrite la_net_cons, IH by lia.
  unfold la_oc. destruct (Z.eqb_spec cap 0) as [E|E]; cbv beta iota;
    destruct (Z.eqb_spec ((no + n) * 2) 0); lia.
Qed.

Lemma la_sl_tr_cnt : forall (P : Z -> bool) live mx no cap len j o, 0 <= cap ->
  ReplyTrPeakW.tr_net_w (fun n => zb (P n)) (send_line_b_c.send_line_tr live mx no cap len j o) =
  la_oc P (send_line_b_c.send_line_cap live mx no cap len) - la_oc P cap.
Proof.
intros P live mx no cap len j o Hc. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
destruct live; [|unfold ReplyTrPeakW.tr_net_w; cbn [fold_right]; lia].
rewrite (la_sl_run_cnt P _ mx no cap len j o Hc), !sl_run_fin. reflexivity.
Qed.

Lemma la_acnt_out : forall (P : Z -> bool) cap out, Z.of_nat (acnt P (aout_blks cap out)) = la_oc P cap.
Proof.
intros P cap out. unfold aout_blks, la_oc. destruct (cap =? 0); [rewrite acnt_nil; reflexivity|].
rewrite acnt_cons, acnt_nil. cbn [snd]. unfold zb. destruct (P cap); reflexivity.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): the segment at a world relation R.  dr_linea_stmt_x / DLL_x / DLN_x /
   DGS_x / DLS_x / DLC_x / LCORE_x / DMEM_x -> their R twins (W_drain_cx_x.v, W_drain_lineb_cx.v), ajournal_gx_x ->
   ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the runs and the branch -> their SRrG forms (W_journal_x.v
   paj_run_to_x_xG, W_kit.v paj_branch_xR), the send_line call -> the engine's W_journal_x.v gx_callS_xR (in place of
   la_callS_x) with the callee spec W_send_line_xR.v sl_spec_xR (SLSPEC_R), the second half LINEB_x -> LINEB_R
   (dr_lineb_stmt_xR), and the journal and cut helpers below -> their R twins.  dr_linea_x below is it at R := wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis SLSPEC_R : sl_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LINEB_R : dr_lineb_stmt_xR B PST ARx MT RP MMAX RG R.
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (R := R) (PI := PI).

(* R twin of la_keep_high_x *)
Lemma la_keep_high_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G ->
@ajournal_gx_xR _ SK SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HGx
  (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* R twin of la_keep_img_x *)
Lemma la_keep_img_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
@ajournal_gx_xR _ SK SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k
  (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hps Hf Hg.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hps Hf).
pose proof (pa_segs_low a Hi) as HL.
apply (aview_gagree SEGS G _ _ _ a Hag). apply inGb_false.
rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
(* R twin of la_keep_blk_x *)
Lemma la_keep_blk_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
@ajournal_gx_xR _ SK SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> ~ inG G (p + i) -> 0 <= p + i < 2 ^ 64 ->
aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k
  (HS0 & HX0 & (memS & HJi & Hag) & _) p n i H1 H2 Hi Hfp Hg Hb.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2 p n i H1 H2 Hi Hfp).
apply (aview_gagree SEGS G _ _ _ (p + i) Hag). apply inGb_false.
rewrite unsigned_lit_small by lia. exact Hg.
Qed.
(* R twin of la_gx_frames_x *)
Lemma la_gx_frames_xR : forall G XO OUT STK sp0 FP ly S Hp W mem md ly' S' Hp' W' mem' md' k,
@ajournal_gx_xR _ SK SEGS B PST ARx R G XO OUT STK sp0 FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
frames S' = frames S.
Proof.
intros G XO OUT STK sp0 FP ly S Hp W mem md ly' S' Hp' W' mem' md' k
  (HS0 & HX0 & (memS & HJi & Hag) & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfr & _). exact Hfr.
Qed.
(* R twin of la_cut_facts_x *)
Lemma la_cut_facts_xR : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
  LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
    spent tl ->
  nozero (drain_b_c.ds_u s1) /\ 0 <= drain_b_c.ds_cap s1 /\ 0 <= dxmx cx /\ 0 <= no /\ 0 <= oc /\ 0 <= ka /\
  0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1).
Proof.
intros cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl HL.
unfold LCORE_xR in HL. cbv zeta in HL. destruct HL as (HM & HK & _ & HH & HR & _).
assert (Pno : drain_b_c.ds_no (dvirt cx s1 sk H ka no oc) = no) by reflexivity.
assert (Poc : drain_b_c.ds_ocap (dvirt cx s1 sk H ka no oc) = oc) by reflexivity.
assert (Pka : drain_b_c.ds_ka (dvirt cx s1 sk H ka no oc) = ka) by reflexivity.
assert (Pen : drain_b_c.ds_en (dvirt cx s1 sk H ka no oc) = drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1))
  by reflexivity.
assert (Pec : drain_b_c.ds_ecap (dvirt cx s1 sk H ka no oc) = drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1))
  by reflexivity.
unfold DMEM_xR in HM. destruct HM as (_ & _ & _ & _ & _ & _ & _ & HE & HS & _ & _ & HO & _).
unfold aentry_okx in HE. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHP & _).
unfold asrc_at in HS.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HX & _).
unfold alist_at in HX. destruct HX as (_ & _ & _ & _ & (HNC & _) & _).
unfold aout_at in HO.
destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Hmx & HOn & HOc).
unfold DLINK in HK. destruct HK as (_ & _ & _ & _ & Eka & _ & _ & _ & _ & Een & Eec & _).
unfold DHIST in HH. destruct HH as (_ & _ & _ & _ & _ & Eno & _).
unfold RSTART in HR. destruct HR as (_ & (_ & _ & _ & HU) & Hcap & _).
rewrite Pno in HOn, Eno. rewrite Poc in HOc. rewrite Pka in Eka. rewrite Pen in Een. rewrite Pec in Eec.
unfold ulen in Hcap.
split; [exact HU|]. split; [lia|]. split; [lia|]. split.
{ revert HOn. destruct (dlive cx); intros HOn; cbn beta iota in HOn; lia. }
split; [destruct HOc as [(Hc0 & _)|(Hc0 & _)]; lia|]. split.
{ rewrite <- Eka. unfold drain_b_c.ent_ka.
  destruct HHP as [(H0 & _)|(H0 & _ & _ & H8 & _)];
    [rewrite (proj2 (Z.eqb_eq _ _) H0) | rewrite (proj2 (Z.eqb_neq _ _) H0)]; lia. }
split; [rewrite <- Een; unfold hl_n; lia|].
rewrite <- Eec. unfold hl_n in HNC. lia.
Qed.
(* R twin of la_cut_dnext_signs_x *)
Lemma la_cut_dnext_signs_xR : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl p,
  0 <= dxmx cx -> dbound s1 p -> no = dlno s1 p -> oc = dloc cx s1 p -> (0 <= ka -> 0 <= dlka cx s1 p) ->
  LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
    spent tl ->
  0 <= oc /\
  0 <= drain_b_c.ds_cap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1).
Proof.
intros cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl p _ HBd Eno Eoc
  Hka HL.
apply la_cut_facts_xR in HL. destruct HL as (HU & Hc & _ & Hno & Hoc & Hk & Hen & Hec).
subst no oc.
destruct (gs_dnext_signs_at cx s1 p HU HBd Hc Hno Hoc (Hka Hk)) as (D1 & D2 & D3 & D4).
repeat split; assumption.
Qed.
Theorem dr_linea_xR : dr_linea_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold dr_linea_stmt_xR. intros cx Hpn kr s1 D p q W1 c1 HB HDLL HN HGS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold DLL_xR in HDLL.
destruct HDLL as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent
  & jb & aa & oo & ha & ks & tl & Hc1 & Hregs & H26 & H23 & H24 & H19 & H25 & Hdib & Hcapp
  & Hbnd & Hpq & Hnulq & Hnoq & HDLC & Hfut).
pose proof Hregs as Hregs'.
unfold dregs_line in Hregs'.
destruct Hregs' as (Hsp & Hr3 & Hr4 & Hr21 & Hr20 & Hr22 & Hr27 & Hr8 & Hr9 & Hr18 & HFRM).
pose proof HFRM as HFRMc. unfold dr_frame in HFRMc.
destruct HFRMc as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144
  & F152 & F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & Fsav).
pose proof HGSB as HGSB0. pose proof HSM as HSM0. pose proof HSD as HSD0.
unfold IMG_TOP in HGSB0, HSM0, HSD0.
pose proof HDLC as HDLC'.
unfold DLC_xR, LCORE_xR in HDLC'.
destruct HDLC' as (HMEM & HLINK & HSAME & HHIST & HRST & HBUD).
pose proof HMEM as HMEM'.
unfold DMEM_xR in HMEM'.
destruct HMEM' as (HJ & HROM & HPRES & HFRAMES & HFR2 & HGARR & HAWR & HEOK & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as HB'.
unfold DBASE_x in HB'.
destruct HB' as (Hafn & HBa0 & Htbl & HSAlo & HSAhi & HSA8 & HBg & HBw & HBeok & HBj4 & HBrest).
destruct Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : DRAIN_STK = 16880) by reflexivity.
(* the cut's journal and the entry's stack room are at DRAIN_STK_x = DRAIN_STK + 128 (W_contract_x.v) *)
assert (WSx : DRAIN_STK_x = 17008) by reflexivity.
assert (HFRAME : DRAIN_FRAME = 352) by reflexivity.
assert (Hdsp : dsp0 cx = spZ (dxregs cx)) by reflexivity.
assert (HSPhi : dsp0 cx <= 2 ^ 47) by lia.
(* ---- the relay entry's block and the two atoms' ranges ---- *)
assert (Htbl1 : In (dxG cx, ATABLE) (ablocks B ly1 S1)).
{ apply (Permutation_in _ (Permutation_sym HPERM)). left. reflexivity. }
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR Htbl1)
  as (HG16 & HG4096 & HGceil & HGia & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil, HGia.
assert (HSAG : dxG cx <= dxSA cx /\ dxSA cx + 56 <= dxG cx + 896)
  by (unfold ATABLE, AENT in HSAlo, HSAhi; lia).
assert (HSA1 : 4096 <= dxSA cx) by lia.
assert (HSA2 : dxSA cx + 56 <= 140737479966720) by lia.
assert (HSAc : dxSA cx + 56 <= alloc_ceiling) by lia.
assert (HSAsp : dxSA cx + 56 <= dsp0 cx - DRAIN_FRAME) by lia.
(* The relay entry's record facts stay PACKED in HEOK: unpacking it puts five disjunctions
   (re_eof, re_skip, re_cap, the buffer and the held array) in the context, and every later `lia`
   then branches over all of them (measured: 30 minutes of wall time).  Each fact below is read out
   of HEOK inside its own subproof, and only non-disjunctive facts are kept. *)
assert (Hpad1 : length (re_pad1 e1) = 4%nat) by (pose proof HEOK as (_ & _ & H & _); exact H).
assert (Hpad2 : length (re_pad2 e1) = 4%nat) by (pose proof HEOK as (_ & _ & _ & H & _); exact H).
assert (HUlen : Z.of_nat (length (re_U e1)) = re_used e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & H & _); exact H).
assert (Husedr : re_used e1 <= re_cap e1)
  by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & H & _); exact H).
assert (HEBL : length (entry_bytes e1) = 56%nat) by (apply la_eb_len; assumption).
assert (HUeq : bzs (re_U e1) = dW s1) by (destruct HLINK as (_ & Hu & _); exact Hu).
assert (Hdwlen : Z.of_nat (length (dW s1)) = re_used e1)
  by (rewrite <- HUeq; unfold bzs; rewrite length_map; exact HUlen).
assert (Hcappos : 0 < re_cap e1) by lia.
assert (HBUF : In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\
  Z.of_nat (length (re_junk e1)) = re_cap e1 - re_used e1 /\
  garr8 SEGS (arm W1 m1) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))).
{ pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  destruct Hb as [(Hc & _ & _)|(_ & Hin & Hj & Hg)]; [lia|].
  split; [exact Hin|]. split; [exact Hj | exact Hg]. }
destruct HBUF as (Hbufin & Hjunk & Hgbuf).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbufin)
  as (HB16 & HB4096 & HBceil & HBia & HBpres & _).
assert (RQB : req_size (re_cap e1) = re_cap e1)
  by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQB in HBceil, HBia.
assert (HBP1 : 4096 <= re_buf e1 + Z.of_nat p) by lia.
assert (HBP2 : re_buf e1 + Z.of_nat p <= 140737479966720) by lia.
assert (HBQ1 : 4096 <= re_buf e1 + Z.of_nat q) by lia.
assert (HBQ2 : re_buf e1 + Z.of_nat q <= 140737479966720) by lia.
(* ---- the environment at the cut ---- *)
set (E := Eimg (Ereg regs1 (la_extra (dxSA cx) (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat q)))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32
  (Ereg regs1 (la_extra (dxSA cx) (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat q))) E)
  by (subst E; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5;
      change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_buf e1 + Z.of_nat p))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_buf e1 + Z.of_nat q))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (U33 : bv_unsigned (ew E 33) = re_buf e1 + Z.of_nat p)
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = re_buf e1 + Z.of_nat q)
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (BV32 : base_val E (Some 32%nat) = dxSA cx)
  by (cbn [base_val]; rewrite E32; apply unsigned_lit_small; lia).
assert (BV2 : base_val E (Some 2%nat) = dsp0 cx - DRAIN_FRAME) by (cbn [base_val]; exact Usp).
(* ---- the four bytes of s->skip, read off the entry's image ---- *)
assert (HSKV : val_mem SEGS (arm W1 m1) (dxSA cx + 8) 4 (re_skip e1)).
{ intros k Hk.
  assert (Hj : ((8 + k) < length (bzs (entry_bytes e1)))%nat) by (rewrite la_len_bzs, HEBL; lia).
  destruct (HGARR (8 + k)%nat Hj) as (Hv & Hr).
  specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv.
  replace (dxSA cx + 8 + Z.of_nat k) with (dxSA cx + Z.of_nat (8 + k)) by lia.
  assert (Hnb : nth (8 + k) (bzs (entry_bytes e1)) 0 = YO0f.le_byte (re_skip e1) 4 k).
  { rewrite la_nth_bzs by (rewrite HEBL; lia). rewrite (la_eb_split e1).
    pose proof (la_pre_len e1) as HL.
    rewrite app_nth2 by lia. rewrite HL.
    replace (8 + k - 8)%nat with k by lia.
    rewrite app_nth1 by (rewrite Mem.length_le4; lia).
    pose proof HEOK as (_ & Hskip & _). destruct Hskip as [Hz|Hz]; rewrite Hz;
    (do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia). }
  rewrite Hv. f_equal. f_equal. rewrite (la_le_byte_1 _ Hr). exact Hnb. }
(* ---- the symbolic entry state, for either value of s->skip ---- *)
assert (HSOK : forall sk, re_skip e1 = sk -> 0 <= sk < 2 ^ 32 ->
  st_ok_pi SEGS VAL E (ss_la sk)
    (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_line)) m1 (seg_rom SEGS)))).
{ intros sk Hsk Hskr. rewrite restrict_mkst_fx. unfold ss_la. apply pa_entry_st_ok_full.
  - unfold la_regs.
    apply regs_ok_pin;
      [ | intros X; discriminate X
      | rewrite (den_atom0 E 34%nat (re_buf e1 + Z.of_nat q) E34) by lia; exact H23 ].
    apply regs_ok_pin;
      [ | intros X; discriminate X
      | rewrite (den_atom0 E 33%nat (re_buf e1 + Z.of_nat p) E33) by lia; exact H24 ].
    subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold la_regions, la_fr, la_ent.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite BV2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 184 8 (SLit 6001) 6001);
          [reflexivity | zside | zside | exact F184].
      * apply (chunk_ok_val SEGS E _ _ 208 8 (SOff 32 8) (dxSA cx + 8));
          [ apply la_den; apply (U_atom_off E 32%nat (dxSA cx) 8 E32); lia
          | cbn; lia | zside | exact F208 ].
      * apply (chunk_ok_val SEGS E _ _ 240 8 (SLit SHADOW_OFF) SHADOW_OFF);
          [reflexivity | first [zside | unfold SHADOW_OFF; cbn; lia] | zside | exact F240].
    + rewrite BV32. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (HAWR o). unfold AENT. lia.
      * repeat apply Forall_cons; try apply Forall_nil.
        apply (chunk_ok_val SEGS E _ _ 8 4 (SLit sk) sk);
          [reflexivity | cbn; lia | zside |].
        rewrite <- Hsk. exact HSKV.
  - apply pairwise_disjoint_of_extents. unfold la_regions, la_fr, la_ent, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite BV2, BV32. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [la_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E33, E34, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold la_CEIL.
    repeat match goal with |- _ /\ _ => split end; try lia.
    rewrite HFRAME, Hdsp, Zminus_mod, Hal16. vm_compute. reflexivity. }
(* ---- the shadow entry over the relay entry's 56 bytes ---- *)
assert (HAPP : forall x, dxSA cx + Z.min 0 56 <= x < dxSA cx + Z.max 0 56 ->
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
{ intros x Hx.
  (* the relay table's block lies in the application range (AR_laws_x's alx_blocks: in_app), off the shadow *)
  clear - HGia HSAG Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. cbn [Z.min Z.max] in Hx. lia. }
assert (SHOK : sh_ok SEGS la_Bx la_SH E (mrestrict (w_H W1) m1)).
{ unfold sh_ok, la_SH. constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H W1) m1 E la_Bx 32%nat (dxSA cx) 56 (dxSA cx) 0 56).
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx) 56 HAR Htbl1);
      (rewrite ?RQT; lia).
  - unfold la_Bx. apply U_lit. unfold SHADOW_OFF. lia.
  - apply (U_atom E 32%nat (dxSA cx) E32). lia.
  - lia.
  - lia.
  - exact HAPP. }
(* ---- DLN after the skip / overlong arm's store of 0 into s->skip ---- *)
assert (DLNOF : forall (regs2 : bvmap 5 word) m2 md2,
  spZ regs2 = dsp0 cx - DRAIN_FRAME ->
  getr regs2 3 = getr (dxregs cx) 3 -> getr regs2 4 = getr (dxregs cx) 4 ->
  getr regs2 21 = w64 (dxSA cx) -> getr regs2 20 = w64 (dxSA cx + 16) ->
  getr regs2 22 = w64 (dxSA cx + 24) -> getr regs2 27 = w64 (dxSA cx + 32) ->
  getr regs2 8 = w64 (rg_s RG) -> getr regs2 9 = w64 (rg_s RG / 8) ->
  getr regs2 18 = w64 ((rg_s RG + 4) / 8) ->
  getr regs2 23 = w64 (re_buf e1 + Z.of_nat q) ->
  val_mem SEGS (arm W1 m2) (dxSA cx + 8) 4 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 8 <= x < dxSA cx + 12) ->
     aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) ->
  (forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m2 x) ->
  @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpn (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
  (dskp s1 p || Nat.ltb LINE_LIMIT (q - p))%bool = true ->
  DLN_xR B PST ARx MT RP MMAX RG R cx Hpn kr s1 D (S q) W1 (cfg_at SEGS (BASE + A_dr_next) regs2 m2 md2)).
{ intros regs2 m2 md2 Hsp2 H3' H4' H21' H20' H22' H27' H8' H9' H18' H23' HVM0 HKEEP HPR2 HJ2 HCOND.
  (* (1) the model: the line is not relayed, so every line-loop value is unchanged *)
  destruct (la_drl_skip s1 p q Hbnd Hpq Hnulq Hnoq HCOND) as (E1 & E2 & E3).
  assert (Edlno : dlno s1 (S q) = dlno s1 p) by (apply la_dlno_eq; exact E1).
  assert (Edlrun : dlrun cx s1 (S q) = dlrun cx s1 p) by (apply la_dlrun_eq; exact E1).
  assert (Edloc : dloc cx s1 (S q) = dloc cx s1 p) by (unfold dloc; rewrite Edlrun; reflexivity).
  assert (EdlH : dlH cx s1 (S q) = dlH cx s1 p) by (unfold dlH; rewrite Edlrun; reflexivity).
  assert (Edlka : dlka cx s1 (S q) = dlka cx s1 p) by (unfold dlka; rewrite Edlrun; reflexivity).
  (* (2) every byte outside the four of s->skip is kept, and writability is kept everywhere *)
  assert (KEPT : forall x, ~ (dxSA cx + 8 <= x < dxSA cx + 12) -> 0 <= x < 2 ^ 64 ->
    abyte_kept W1 m1 W1 m2 x).
  { intros x Hx Hr. split; [apply HKEEP; assumption|].
    unfold arm. apply writable_kept. intros Hp. exact (HPR2 x Hp). }
  assert (WRK : forall x, writable_at SEGS (arm W1 m1) x -> writable_at SEGS (arm W1 m2) x).
  { intros x Hw. exact (writable_kept (w_H W1) m1 m2 x (fun Hp => HPR2 x Hp) Hw). }
  (* (3) s->skip's four bytes lie in the relay table's block, so they are no image byte and no byte of
         any other live block *)
  assert (HIMG : forall a, in_img SEGS a -> ~ (dxSA cx + 8 <= a < dxSA cx + 12)).
  { intros a Hi Hx.
    apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE a HAR Htbl1);
      [rewrite RQT; lia | exact Hi]. }
  assert (HIMGr : forall a, in_img SEGS a -> 0 <= a < 2 ^ 64).
  { intros a Hi. pose proof (Hsegs a Hi) as HL. unfold kLowMemEnd in HL. lia. }
  pose proof (Permutation_NoDup HPERM (la_ablocks_nodup_x ly1 S1 Hp1 W1 m1 md1 HAR)) as NDall.
  apply NoDup_cons_iff in NDall. destruct NDall as (Hni & _).
  assert (HBLKo : forall b n a, In (b, n) (ablocks B ly1 S1) -> (b, n) <> (dxG cx, ATABLE) ->
    b <= a < b + req_size n -> ~ (dxSA cx + 8 <= a < dxSA cx + 12)).
  { intros b n a Hin Hne Ha Hx.
    pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 b n (dxG cx) ATABLE HAR Hin Htbl1 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite RQT in Hd. lia. }
  assert (HBLKr : forall b n a, In (b, n) (ablocks B ly1 S1) -> b <= a < b + req_size n ->
    0 <= a < 2 ^ 64).
  { intros b n a Hin Ha.
    destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 b n HAR Hin) as (_ & Hb4 & Hbc & _). lia. }
  (* the blocks the entry, the harness source and the controller name are blocks of S1, none of them the
     relay table's block (the permutation lists that one separately and ablocks has no duplicate) *)
  assert (HINe : forall bn, In bn (aentry_blks e1) ->
    In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)).
  { intros bn Hin. split.
    - apply (Permutation_in _ (Permutation_sym HPERM)). right. apply in_or_app. left. exact Hin.
    - intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. left. exact Hin. }
  assert (HINs : forall bn, In bn (asrc_blks h1) ->
    In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)).
  { intros bn Hin. split.
    - apply (Permutation_in _ (Permutation_sym HPERM)). right. apply in_or_app. right.
      apply in_or_app. left. exact Hin.
    - intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. right. apply in_or_app. left. exact Hin. }
  assert (HINo : forall bn, In bn (aout_blks (drain_b_c.ds_ocap
      (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) out1) ->
    In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)).
  { intros bn Hin. split.
    - apply (Permutation_in _ (Permutation_sym HPERM)). right. apply in_or_app. right.
      apply in_or_app. right. apply in_or_app. left. exact Hin.
    - intros Heq. apply Hni. rewrite <- Heq. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact Hin. }
  (* (4) the three footprints are kept *)
  assert (KEPTblk : forall bn a, In bn (ablocks B ly1 S1) -> bn <> (dxG cx, ATABLE) ->
    fst bn <= a < fst bn + req_size (snd bn) -> abyte_kept W1 m1 W1 m2 a).
  { intros bn a Hin Hne Ha. destruct bn as [b n]. cbn [fst snd] in Ha.
    apply KEPT; [exact (HBLKo b n a Hin Hne Ha) | exact (HBLKr b n a Hin Ha)]. }
  assert (KEPTimg : forall a, in_img SEGS a -> abyte_kept W1 m1 W1 m2 a).
  { intros a Hi. apply KEPT; [exact (HIMG a Hi) | exact (HIMGr a Hi)]. }
  assert (KEPTe2 : forall b n a, In (b, n) (aentry_blks e1) -> b <= a < b + req_size n ->
    abyte_kept W1 m1 W1 m2 a).
  { intros b n a Hin Ha.
    exact (KEPTblk (b, n) a (proj1 (HINe _ Hin)) (proj2 (HINe _ Hin)) Ha). }
  assert (KEPTent : akept W1 m1 W1 m2 (aentry_fp e1)).
  { intros r Hr a Ha. unfold aentry_fp in Hr.
    destruct (Z.eqb_spec (re_cap e1) 0) as [Hc0|Hc0]; [lia|]. cbn [app In] in Hr.
    destruct Hr as [<- | [<- | Hr]].
    - (* the buffer *)
      unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, length_app in Ha.
      apply (KEPTe2 (re_buf e1) (re_cap e1) a); [|rewrite RQB; lia].
      unfold aentry_blks. apply in_or_app. left.
      destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. left. reflexivity.
    - (* the held array *)
      unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, la_key_ptrs_len in Ha.
      pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hheld & _).
      destruct Hheld as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
      + exfalso. rewrite Hke in Ha. cbn [length] in Ha. lia.
      + pose proof (BLKN ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as Hn0.
        pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (_ & Hrq).
        unfold re_nheld in Hk1.
        apply (KEPTe2 (re_hp e1) (re_kh e1) a); [|lia].
        unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
        destruct (Z.eqb_spec (re_hp e1) 0); [lia|]. left. reflexivity.
    - (* a held key *)
      apply in_map_iff in Hr. destruct Hr as (kk & Hre & Hkk). subst r.
      unfold gfp in Ha. cbn [fst snd] in Ha.
      rewrite la_len_bzs, length_app in Ha. cbn [length] in Ha.
      pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkeys).
      rewrite Forall_forall in Hkeys. destruct (Hkeys kk Hkk) as (Hin & _ & _ & Hlen).
      pose proof (req_size_pos (Z.of_nat (length (key_text kk)) + 1) ltac:(lia)) as (_ & Hrq).
      apply (KEPTe2 (key_addr kk) (Z.of_nat (length (key_text kk)) + 1) a); [|lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply in_map_iff. exists kk. split; [reflexivity | exact Hkk]. }
  (* (5) the cells of g_s and of the controller are image bytes (gx_ok of G_DR, and of HGO's three cells), a block
     byte is not (blk_img_x, AR_laws_x's alx_client_img), so none of them is one of the four bytes the store wrote *)
  assert (HGimg : forall a, inG (G_DR B RG) a -> in_img SEGS a) by (intros a Ha; exact (proj1 (HG a Ha))).
  assert (HGOimg : forall a, inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a -> in_img SEGS a)
    by (intros a Ha; exact (proj1 (HGO a Ha))).
  assert (KEPTgs : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W1 m2 a).
  { intros a Ha. apply KEPTimg. apply HGimg. unfold inG, G_DR. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    lia. }
  (* (6) the frame lies above the allocator ceiling, so the store misses it *)
  assert (KEPTfr : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W1 m2 x).
  { intros x Hx. apply KEPT; [lia | lia]. }
  (* (7) the relay entry's image after the store: the prefix and the tail are kept, the skip word is 0 *)
  assert (HGARRn : garr8 SEGS (arm W1 m2) (dxSA cx) (bzs (entry_bytes (la_sk0 e1)))).
  { assert (Hsp0 : entry_bytes (la_sk0 e1) = la_pre e1 ++ Mem.le4 (Z_to_bv 64 0) ++ la_post e1)
      by (rewrite (la_eb_split (la_sk0 e1)); reflexivity).
    pose proof (la_eb_split e1) as Hsp1.
    assert (HPOSTL : length (la_post e1) = 44%nat).
    { pose proof HEBL as HL56. rewrite (la_eb_split e1), !length_app, la_pre_len, Mem.length_le4 in HL56.
      lia. }
    rewrite Hsp0. rewrite Hsp1 in HGARR.
    rewrite (la_bzs_app (la_pre e1)) in HGARR |- *.
    rewrite (la_bzs_app (Mem.le4 (Z_to_bv 64 (re_skip e1)))) in HGARR.
    rewrite (la_bzs_app (Mem.le4 (Z_to_bv 64 0))).
    apply garr8_app in HGARR. destruct HGARR as (HGa & HGbc).
    apply garr8_app in HGbc. destruct HGbc as (HGb & HGc).
    rewrite la_len_bzs, la_pre_len in HGb, HGc.
    rewrite la_len_bzs, Mem.length_le4 in HGc.
    apply garr8_app. split.
    - apply (akept_garr8 W1 m1 W1 m2); [|exact HGa].
      intros x Hx. rewrite la_len_bzs, la_pre_len in Hx.
      apply KEPT; [lia | lia].
    - rewrite la_len_bzs, la_pre_len. apply garr8_app. split.
      + rewrite la_bzs_zero4. intros j Hj. cbn [length] in Hj.
        assert (Hv : val_mem SEGS (arm W1 m2) (dxSA cx + Z.of_nat 8 + Z.of_nat j) 1 0).
        { intros kk Hkk. assert (Hkk0 : kk = 0%nat) by lia. subst kk.
          rewrite Z.add_0_r. specialize (HVM0 j ltac:(lia)).
          rewrite la_le_byte_0 in HVM0. rewrite la_le_byte_0.
          replace (dxSA cx + Z.of_nat 8 + Z.of_nat j) with (dxSA cx + 8 + Z.of_nat j) by lia.
          exact HVM0. }
        split; [|do 4 (destruct j as [|j]; [cbn [nth]; lia|]); lia].
        replace (nth j [0; 0; 0; 0] 0) with 0
          by (do 4 (destruct j as [|j]; [reflexivity|]); lia).
        exact Hv.
      + rewrite la_len_bzs, Mem.length_le4.
        apply (akept_garr8 W1 m1 W1 m2); [|exact HGc].
        intros x Hx. rewrite la_len_bzs in Hx.
        apply KEPT; [lia | lia]. }
  (* (8) the entry's own facts survive *)
  assert (HAWRn : awr W1 m2 (dxSA cx) AENT) by (intros o Ho; apply WRK; exact (HAWR o Ho)).
  assert (HEOKn : aentry_okx B ly1 S1 W1 m2 (la_sk0 e1)).
  { unfold aentry_okx, la_sk0 in *.
    cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk
         re_nheld] in *.
    pose proof HEOK as (Heof & _ & _ & _ & Hfd & Hcapr & _ & _ & Hbufc & Hnheld & Hheld & HND1 & HND2
      & Hkeys).
    split; [exact Heof|]. split; [left; reflexivity|].
    split; [exact Hpad1|]. split; [exact Hpad2|]. split; [exact Hfd|].
    split; [exact Hcapr|]. split; [exact HUlen|]. split; [exact Husedr|].
    split.
    { destruct Hbufc as [(Hc & _)|(Hc & Hin & Hj & Hg)]; [lia|].
      right. split; [exact Hc|]. split; [exact Hin|]. split; [exact Hj|].
      apply (akept_garr8 W1 m1 W1 m2); [|exact Hg].
      intros x Hx. apply (KEPTent (gfp (re_buf e1) (bzs (re_U e1 ++ re_junk e1)))).
      - unfold aentry_fp. apply in_or_app. left.
        destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. left. reflexivity.
      - cbn [fst snd]. exact Hx. }
    split; [exact Hnheld|].
    split.
    { destruct Hheld as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & Hg)]; [left; split; assumption|].
      right. split; [exact Hz|]. split; [exact Hin|]. split; [exact Hk1|]. split; [exact Hk2|].
      apply (akept_garr8 W1 m1 W1 m2); [|exact Hg].
      intros x Hx. apply (KEPTent (gfp (re_hp e1) (bzs (key_ptrs (re_keys e1))))).
      - unfold aentry_fp. apply in_or_app. right. left. reflexivity.
      - cbn [fst snd]. exact Hx. }
    split; [exact HND1|]. split; [exact HND2|].
    rewrite Forall_forall in Hkeys |- *. intros kk Hkk.
    destruct (Hkeys kk Hkk) as (Hin & Hg & Hnz & Hlen).
    split; [exact Hin|]. split; [|split; [exact Hnz | exact Hlen]].
    apply (akept_garr8 W1 m1 W1 m2); [|exact Hg].
    intros x Hx. apply (KEPTent (gfp (key_addr kk) (bzs (key_text kk ++ [Z_to_bv 8 0])))).
    - unfold aentry_fp. apply in_or_app. right. right.
      apply in_map_iff. exists kk. split; [reflexivity | exact Hkk].
    - cbn [fst snd]. exact Hx. }
  (* (9) the harness source and the controller's output: their footprints are image cells and blocks of
     S1 other than the relay table's *)
  assert (ABKT : forall (Wa : world SEGS) ma (Wb : world SEGS) mb (Wc : world SEGS) mc a,
    abyte_kept Wa ma Wb mb a -> abyte_kept Wb mb Wc mc a -> abyte_kept Wa ma Wc mc a).
  { intros Wa ma Wb mb Wc mc a (Hv1 & Hw1) (Hv2 & Hw2).
    split; [rewrite Hv2; exact Hv1 | intros Hh; exact (Hw2 (Hw1 Hh))]. }
  assert (HJ4 : (dxj cx < 4)%nat) by exact HBj4.
  assert (HHAgs : forall a, dHA RG cx <= a < dHA RG cx + ASRC -> rg_s RG <= a < rg_s RG + 4 * ASRC).
  { intros a Ha. unfold dHA in *. unfold ASRC in *. lia. }
  assert (KEPTlist : forall LA l lines0,
    alist_at B ly1 S1 W1 m1 LA l lines0 ->
    (forall x, LA <= x < LA + 16 -> abyte_kept W1 m1 W1 m2 x) ->
    (forall bn, In bn (alist_blks l) -> In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)) ->
    akept W1 m1 W1 m2 (alist_fp LA l)).
  { intros LA l lines0 HL HLA HB2 r Hr a Ha.
    pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
    unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
    - cbn [fst snd] in Ha. exact (HLA a Ha).
    - apply in_app_or in Hr. destruct Hr as [Hr|Hr].
      + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
        destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
        rewrite la_len_bzs, length_app, la_recs_len in Ha.
        destruct Hv as [(Hc & _)|(_ & Hin & Hj & _)]; [lia|].
        unfold hl_n in *. unfold AREC in *.
        pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
        unfold AREC in Hrq.
        apply (KEPTblk (hl_v l, AREC * hl_cap l) a);
          [ exact (proj1 (HB2 _ ltac:(unfold alist_blks; apply in_or_app; left;
              destruct (Z.eqb_spec (hl_cap l) 0); [lia|]; left; reflexivity)))
          | exact (proj2 (HB2 _ ltac:(unfold alist_blks; apply in_or_app; left;
              destruct (Z.eqb_spec (hl_cap l) 0); [lia|]; left; reflexivity)))
          | cbn [fst snd]; unfold AREC; lia ].
      + apply in_map_iff in Hr. destruct Hr as (rr & Hre & Hrr). subst r.
        unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, length_app in Ha. cbn [length] in Ha.
        rewrite Forall_forall in Hrecs. destruct (Hrecs rr Hrr) as (Hin & _).
        pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as (_ & Hrq).
        apply (KEPTblk (fst rr, Z.of_nat (length (snd rr)) + 1) a);
          [ exact (proj1 (HB2 _ ltac:(unfold alist_blks; apply in_or_app; right;
              apply in_map_iff; exists rr; split; [reflexivity | exact Hrr])))
          | exact (proj2 (HB2 _ ltac:(unfold alist_blks; apply in_or_app; right;
              apply in_map_iff; exists rr; split; [reflexivity | exact Hrr])))
          | cbn [fst snd]; lia ]. }
  assert (KEPTsrc : akept W1 m1 W1 m2 (asrc_fp (dHA RG cx) h1)).
  { pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj
      & _ & _ & Hexp & Hhld & _).
    intros r Hr a Ha. unfold asrc_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | Hr]].
    - cbn [fst snd] in Ha. apply KEPTgs. exact (HHAgs a Ha).
    - unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs in Ha.
      pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
      apply (KEPTblk (hs_partial h1, APARTIAL) a);
        [ exact (proj1 (HINs _ ltac:(unfold asrc_blks; left; reflexivity)))
        | exact (proj2 (HINs _ ltac:(unfold asrc_blks; left; reflexivity)))
        | cbn [fst snd]; lia ].
    - apply in_app_or in Hr. destruct Hr as [Hr|Hr].
      + apply (KEPTlist (dHA RG cx + 16) (hs_pending h1) false Hpend
          ltac:(intros x Hx; apply KEPTgs; apply HHAgs; unfold ASRC in *; lia)
          ltac:(intros bn Hbn; apply HINs; unfold asrc_blks; right; apply in_or_app; left; exact Hbn)
          r Hr a Ha).
      + apply in_app_or in Hr. destruct Hr as [Hr|Hr].
        * apply (KEPTlist (dHA RG cx + 64) (hs_expected h1) true Hexp
            ltac:(intros x Hx; apply KEPTgs; apply HHAgs; unfold ASRC in *; lia)
            ltac:(intros bn Hbn; apply HINs; unfold asrc_blks; right; apply in_or_app; right;
                  apply in_or_app; left; exact Hbn)
            r Hr a Ha).
        * apply (KEPTlist (dHA RG cx + 80) (hs_held h1) true Hhld
            ltac:(intros x Hx; apply KEPTgs; apply HHAgs; unfold ASRC in *; lia)
            ltac:(intros bn Hbn; apply HINs; unfold asrc_blks; right; apply in_or_app; right;
                  apply in_or_app; right; exact Hbn)
            r Hr a Ha). }
  assert (KEPTout : akept W1 m1 W1 m2
    (aout_fp B RG (drain_b_c.ds_ocap
       (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) out1)).
  { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & Hblk).
    set (OC := drain_b_c.ds_ocap
      (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) in *.
    intros r Hr a Ha. unfold aout_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
      cbn [fst snd] in Ha.
    - apply KEPTimg. apply HGOimg. unfold inG. apply Exists_exists.
      exists (rg_send_max RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTimg. apply HGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (rg_nout RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTimg. apply HGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (rg_capout RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTimg. apply HGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (rg_out RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTimg. apply HGOimg. unfold inG. apply Exists_exists.
      exists (rg_client RG, 4). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTimg. apply HGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (rg_client_broken RG, 1). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTimg. apply HGOimg. unfold inG. apply Exists_exists.
      exists (rg_send_dead RG, 1). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTimg. apply HGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (rg_send_eintr RG, 1). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - apply KEPTimg. apply HGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
      exists (as_errno B, 4). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
    - destruct (Z.eqb_spec OC 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
      destruct Hr as [<- | []]. cbn [fst snd] in Ha.
      destruct Hblk as [(Hc & _)|(_ & _ & Hin & _)]; [exfalso; exact (Hc0 Hc)|].
      assert (Hrq : req_size OC = OC)
        by (unfold req_size; destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia | reflexivity]).
      apply (KEPTblk (out1, OC) a);
        [ exact (proj1 (HINo _ ltac:(unfold aout_blks;
            destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia|]; left; reflexivity)))
        | exact (proj2 (HINo _ ltac:(unfold aout_blks;
            destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia|]; left; reflexivity)))
        | cbn [fst snd]; rewrite Hrq; lia ]. }
  (* (10) the DLN cut at S q *)
  exists regs2, ly1, S1, Hp1, m2, md2, k1, (la_sk0 e1), h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl.
  split; [reflexivity|].
  split.
  {
    unfold dregs_line, dr_frame.
    split; [exact Hsp2|]. split; [exact H3'|]. split; [exact H4'|]. split; [exact H21'|].
    split; [exact H20'|]. split; [exact H22'|]. split; [exact H27'|]. split; [exact H8'|].
    split; [exact H9'|]. split; [exact H18'|].
    repeat split;
      try (eapply akept_vm; [intros x Hx; apply KEPTfr; unfold DRAIN_FRAME in *; lia | eassumption]).
    intros i Hi. eapply akept_vm;
      [intros x Hx; apply KEPTfr; unfold DRAIN_FRAME, DR_SAVE_OFF in *; lia | exact (Fsav i Hi)]. }
  split.
  { replace (re_buf (la_sk0 e1) + Z.of_nat (S q) - 1) with (re_buf e1 + Z.of_nat q)
      by (cbn [la_sk0 re_buf]; lia).
    exact H23'. }
  split; [cbn [la_sk0 re_buf re_cap]; exact Hdib|]. split; [cbn [la_sk0 re_buf re_cap]; exact Hcapp|].
  split; [split; [lia | right; replace (S q - 1)%nat with q by lia; exact Hnulq]|].
  split; [lia|].
  split.
  { unfold DLC_xR, LCORE_xR. rewrite E1, E3, Edlno, Edloc, EdlH, Edlka, <- E2.
    split.
    { unfold DMEM_xR.
      split; [exact HJ2|].
      split.
      { intros a Hrom.
        assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hin & _ & Hrr); exists sg; split; assumption).
        rewrite HKEEP; [exact (HROM a Hrom) | exact (HIMGr a Hi) | exact (HIMG a Hi)]. }
      split; [intros a Hi Ho He Hp; apply HPR2; exact (HPRES a Hi Ho He Hp)|].
      split; [exact HFRAMES|].
      split.
      {
        unfold dr_frame.
        repeat split;
        try (eapply akept_vm; [intros x Hx; apply KEPTfr; unfold DRAIN_FRAME in *; lia | eassumption]).
        intros i Hi. eapply akept_vm;
          [intros x Hx; apply KEPTfr; unfold DRAIN_FRAME, DR_SAVE_OFF in *; lia | exact (Fsav i Hi)]. }
      split; [exact HGARRn|].
      split; [exact HAWRn|].
      split; [exact HEOKn|].
      split.
      { exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 HSRC KEPTsrc
          ltac:(intros bn Hbn; exact (proj1 (HINs bn Hbn)))). }
      split.
      { intros i Hi Hne. destruct (HOTH i Hi Hne) as (f & o & V1 & V2 & Hd).
        exists f, o. split.
        { eapply akept_vm; [intros x Hx; apply KEPTgs; unfold ASRC in *; lia | exact V1]. }
        split; [|exact Hd].
        eapply akept_vm; [intros x Hx; apply KEPTgs; unfold ASRC in *; lia | exact V2]. }
      split.
      { intros x Hx Hnx. apply (ABKT (dxW cx) (dxmem cx) W1 m1 W1 m2 x); [exact (HKEPT x Hx Hnx)|].
        exact (KEPTgs x Hx). }
      split.
      { exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2 _ _ _ _ _ out1 HOUT KEPTout
          ltac:(intros bn Hbn; exact (proj1 (HINo bn Hbn)))). }
      split; [exact HLIVE|].
      exact HPERM. }
    split.
    { unfold DLINK in HLINK |- *.
      cbn [la_sk0 re_cap re_U re_skip re_keys re_hp re_kh] in *.
      destruct HLINK as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
      split; [exact L1|]. split; [exact L2|]. split; [reflexivity|].
      split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|].
      split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact L11|]. exact L12. }
    split; [exact HSAME|].
    split; [exact HHIST|].
    split; [exact HRST | exact HBUD]. }
  rewrite Edlno, Edloc, EdlH, Edlka, <- E2. exact Hfut. }
(* ---- the two arms of the skip / overlong test ---- *)
rewrite Hc1. unfold cfg_at. change (w64 (BASE + A_dr_line)) with (Z_to_bv 64 (BASE + A_dr_line)).
pose proof HEOK as (_ & Hskip & _). destruct Hskip as [Hsk0|Hsk1].
- (* s->skip = 0: the length test decides *)
  pose proof (HSOK 0 Hsk0 ltac:(lia)) as HS.
  (* decide `bltu a1,a2,839e8` (0x839c4) on the entry state, so each arm runs exactly once: the `sub` at
     0x839bc normalises to this linear form, and the condition goes into the state's facts *)
  apply (BRR W1 E (ss_la 0) _ _ _ BC_LTU
    (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SOff 34 0)) (SLit 6001) HS);
    clear HS; intros Hc HS.
  + (* taken: nul - start < 6001, so the line is relayed by send_line *)
    rewrite branch_ltu_U in Hc.
    rewrite (la_U_diff E 33%nat 34%nat _ _ U33 U34 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
    rewrite U_SLit in Hc. change (zcanon 6001) with 6001 in Hc.
    apply Z.ltb_lt in Hc.
    (* 0x8399c .. 0x839f0: the shadow and skip tests, the length, the start, and `jal send_line`; stop at send_line's entry *)
    paj_run_to_tok_xR RUNTOR HS HJ SHOK la_Bspan AF_fr_send_line.
    { unfold ss_la, la_regions, la_fr, la_ent. cbn [ss_mem].
      apply awr_ok_x_cons.
      - cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. intros a Ha. exfalso. clear - Ha. lia.
      - apply awr_ok_x_cons; [|apply awr_ok_x_nil].
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. rewrite BV32. intros a Ha.
        left. split; [|lia]. right. left. split.
        + unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
          cbn [fst snd]. unfold AENT. lia.
        + exists (dxG cx), ATABLE. split; [exact Htbl1|]. rewrite RQT. lia. }
    (* s->skip's four bytes at the call, read off the entry region (the run stored nothing; they hold 0) *)
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ev ?ssF ?msF =>
        pose proof (st_ok_pi_region_nth Ev ssF msF 1 _ HS eq_refl) as RGents
    end.
    cbn [ms_mem restrict] in RGents.
    assert (LAVMs : val_mem SEGS (arm W1 (ms_mem ms)) (dxSA cx + 8) 4 0).
    { change 4%nat with (N.to_nat 4).
      eapply (field_of_region _ _ 32%nat (dxSA cx) _ _ _ _ _ 8 4 (SLit 0) 0);
        [ exact RGents
        | rewrite E32; apply unsigned_lit_small; lia
        | left; reflexivity
        | reflexivity
        | cbn; lia
        | cbn; lia ]. }
    clear RGents.
    pmkst HS.
    prreg HS (1%bv : bv 5) S1r. prreg HS (2%bv : bv 5) S2r. prreg HS (3%bv : bv 5) S3r.
    prreg HS (4%bv : bv 5) S4r. prreg HS (8%bv : bv 5) S8r.
    prreg HS (10%bv : bv 5) S10. prreg HS (11%bv : bv 5) S11.
    prreg HS (9%bv : bv 5) S9r. prreg HS (18%bv : bv 5) S18r. prreg HS (21%bv : bv 5) S21r.
    prreg HS (22%bv : bv 5) S22r. prreg HS (23%bv : bv 5) S23r. prreg HS (24%bv : bv 5) S24r.
    prreg HS (27%bv : bv 5) S27r. prreg HS (20%bv : bv 5) S20r.
    (* The line, with its NUL: a window of the relay buffer's bytes. *)
    assert (HUL : length (re_U e1) = length (dW s1))
      by (rewrite <- HUeq; symmetry; apply la_len_bzs).
    (* the relay buffer is not g_out's block: if g_out has no block, out1 is 0 and the buffer is not;
       otherwise two live blocks with the same base are the same block, which ablocks' NoDup forbids. *)
    assert (HBUFO : re_buf e1 <> out1).
    { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & Hblk0).
      destruct Hblk0 as [(Hc0 & Ho0 & _)|(_ & _ & Hin0 & _)]; [rewrite Ho0; clear - HB4096; lia|].
      intros Heq.
      assert (DEC0 : forall x y : Z * Z, {x = y} + {x <> y}).
      { intros [x1 x2] [y1 y2]. destruct (Z.eq_dec x1 y1) as [->|N1]; [|right; congruence].
        destruct (Z.eq_dec x2 y2) as [->|N2]; [left; reflexivity | right; congruence]. }
      destruct (DEC0 (re_buf e1, re_cap e1)
        (out1, drain_b_c.ds_ocap
           (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p)))) as [Hpe|Hpe].
      - pose proof (Permutation_NoDup HPERM (la_ablocks_nodup_x ly1 S1 Hp1 W1 m1 md1 HAR)) as NDb.
        apply NoDup_cons_iff in NDb. destruct NDb as (_ & NDb).
        refine (la_nodup_app_disj _ _ _ (re_buf e1, re_cap e1) NDb _ _).
        + unfold aentry_blks. apply in_or_app. left.
          destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. left. reflexivity.
        + apply in_or_app. right. apply in_or_app. left.
          injection Hpe as Hb2 Hc2.
          assert (HOCpos : 0 < drain_b_c.ds_ocap
            (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p)))
            by (rewrite <- Hc2; exact Hcappos).
          unfold aout_blks.
          destruct (Z.eqb_spec (drain_b_c.ds_ocap
            (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) 0) as [Hz|Hz].
          * exfalso. rewrite Hz in HOCpos. exact (Z.lt_irrefl 0 HOCpos).
          * left. rewrite Hb2, Hc2. reflexivity.
      - pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) out1 _
          HAR Hbufin Hin0 Hpe) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd.
        pose proof (BLKN ly1 S1 Hp1 W1 m1 md1 out1 _ HAR Hin0) as Hn0.
        pose proof (req_size_pos _ Hn0) as (Hrp & _).
        rewrite RQB in Hd. clear - Hd Heq Hcappos Hrp. lia. }
    assert (HBLL : length (firstn (q - p + 1) (skipn p (re_U e1))) = (q - p + 1)%nat).
    { rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn.
      assert (HU : length (re_U e1) = length (dW s1))
        by (rewrite <- HUeq; symmetry; apply la_len_bzs).
      clear - HU Hpq. lia. }
    assert (HADS : A_dr_send = 5808) by (vm_compute; reflexivity).
    (* la_live_bridge's side condition, dr_tot (dxh cx) <> 0: W_drain_ref.v dr_ref_line gives dref s1 <> [] at
       the line in hand, and DHIST's dPS cx = (D ++ ddata s1) ++ pstream sv with RSTART's ds_ref s1 =
       feed (dSTR cx) D put dref s1 inside the drain's reference lines (RelayModel.v lines_app, twice). *)
    assert (LASK : dskp s1 p = false).
    { destruct HLINK as (_ & _ & Hs & _). destruct (dskp s1 p); [|reflexivity].
      cbn [drain_b_c.ds_skip dvirt] in Hs. lia. }
    (* LINE_LIMIT is a unary nat literal: go through Z *)
    assert (HLL : (q - p <= LINE_LIMIT)%nat).
    { apply Nat2Z.inj_le. rewrite Nat2Z.inj_sub by (clear - Hpq; lia).
      assert (LALLZ : Z.of_nat LINE_LIMIT = 6000) by (vm_compute; reflexivity).
      rewrite LALLZ. clear - Hc. lia. }
    assert (DRTOT : dr_tot (dxh cx) <> 0).
    { pose proof HRST as (HRref & HJ1 & _).
      pose proof HHIST as (HPS & _).
      assert (HDR : dref s1 <> []) by (eapply (dr_ref_line s1 p q); eassumption).
      assert (HWN : forall l1 l2, with_nul (l1 ++ l2) = with_nul l1 ++ with_nul l2)
        by (intros l1 l2; unfold with_nul; rewrite map_app, concat_app; reflexivity).
      assert (HWP : forall l, l <> [] -> (0 < length (with_nul l))%nat).
      { intros [|x r] Hl; [contradiction|]. unfold with_nul. cbn [map concat].
        rewrite !length_app. cbn [length]. lia. }
      unfold dr_tot, dr_lines.
      change (bzs (pending_stream (dxh cx))) with (dPS cx).
      change (hs_state (dxh cx)) with (dSTR cx).
      rewrite HPS, <- app_assoc, RelayModel.lines_app, RelayModel.lines_app, <- HRref.
      change (lines (drain_b_c.ds_ref s1) (ddata s1)) with (dref s1).
      rewrite !HWN, !length_app.
      pose proof (HWP (dref s1) HDR) as HPw0. clear - HPw0. lia. }
    (* The run from the branch to the call stores nothing, so DMEM's memory facts carry to ms_mem ms. *)
    lazymatch goal with
    | HFx : frame_of ?Ev ?rs _ _ |- _ =>
        assert (SKEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 8 <= x < dxSA cx + 12) ->
          aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x)
        by (intros x Hx Hnx;
            apply (aview_kept_out Ev rs (w_H W1) m1 (ms_mem ms) HFx x Hx);
            intros (rr & Hin & Hr);
            unfold ss_la, la_regions, la_fr, la_ent in Hin; cbn [ss_mem add_cond In] in Hin;
            destruct Hin as [<- | [<- | []]];
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?BV32, ?BV2 in Hr; lia)
    end.
    lazymatch goal with
    | HGx : mem_grows _ _ |- _ =>
        assert (SPRES : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x)
          by (intros x Hp; exact (apresent_grows (w_H W1) m1 (ms_mem ms) x HGx Hp))
    end.
    assert (SKEPT : forall x, ~ (dxSA cx + 8 <= x < dxSA cx + 12) -> 0 <= x < 2 ^ 64 ->
      abyte_kept W1 m1 W1 (ms_mem ms) x).
    { intros x Hx Hr. split; [apply SKEEP; assumption|].
      unfold arm. apply writable_kept. intros Hp. exact (SPRES x Hp). }
    assert (SIMG : forall a, in_img SEGS a -> ~ (dxSA cx + 8 <= a < dxSA cx + 12)).
    { intros a Hi Hx.
      apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE a HAR Htbl1);
        [rewrite RQT; lia | exact Hi]. }
    assert (SIMGr : forall a, in_img SEGS a -> 0 <= a < 2 ^ 64).
    { intros a Hi. pose proof (Hsegs a Hi) as HL. unfold kLowMemEnd in HL. lia. }
    (* the cells of g_s and of the controller are image bytes (gx_ok of G_DR, and of HGO's three cells) *)
    assert (SKIMG : forall a, in_img SEGS a -> abyte_kept W1 m1 W1 (ms_mem ms) a)
      by (intros a Hi; apply SKEPT; [exact (SIMG a Hi) | exact (SIMGr a Hi)]).
    assert (SGimg : forall a, inG (G_DR B RG) a -> in_img SEGS a) by (intros a Ha; exact (proj1 (HG a Ha))).
    assert (SGOimg : forall a, inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a -> in_img SEGS a)
      by (intros a Ha; exact (proj1 (HGO a Ha))).
    pose proof (Permutation_NoDup HPERM (la_ablocks_nodup_x ly1 S1 Hp1 W1 m1 md1 HAR)) as NDs.
    apply NoDup_cons_iff in NDs. destruct NDs as (Hnis & _).
    assert (SBLKo : forall b n a, In (b, n) (ablocks B ly1 S1) -> (b, n) <> (dxG cx, ATABLE) ->
      b <= a < b + req_size n -> ~ (dxSA cx + 8 <= a < dxSA cx + 12)).
    { intros b n a Hin Hne Ha Hx.
      pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 b n (dxG cx) ATABLE HAR Hin Htbl1 Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite RQT in Hd. lia. }
    assert (SKBLK : forall bn a, In bn (ablocks B ly1 S1) -> bn <> (dxG cx, ATABLE) ->
      fst bn <= a < fst bn + req_size (snd bn) -> abyte_kept W1 m1 W1 (ms_mem ms) a).
    { intros bn a Hin Hne Ha. destruct bn as [b n]. cbn [fst snd] in Ha.
      apply SKEPT; [exact (SBLKo b n a Hin Hne Ha)|].
      destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 b n HAR Hin) as (_ & Hb4 & Hbc & _). lia. }
    assert (SINe : forall bn, In bn (aentry_blks e1) ->
      In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)).
    { intros bn Hin. split.
      - apply (Permutation_in _ (Permutation_sym HPERM)). right. apply in_or_app. left. exact Hin.
      - intros Heq. apply Hnis. rewrite <- Heq. apply in_or_app. left. exact Hin. }
    assert (SINo : forall bn, In bn (aout_blks (drain_b_c.ds_ocap
        (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) out1) ->
      In bn (ablocks B ly1 S1) /\ bn <> (dxG cx, ATABLE)).
    { intros bn Hin. split.
      - apply (Permutation_in _ (Permutation_sym HPERM)). right. apply in_or_app. right.
        apply in_or_app. right. apply in_or_app. left. exact Hin.
      - intros Heq. apply Hnis. rewrite <- Heq. apply in_or_app. right. apply in_or_app. right.
        apply in_or_app. left. exact Hin. }
    (* rom_view and the relay buffer at the call *)
    assert (SROM : rom_view SEGS W1 (ms_mem ms)).
    { intros a Hrom.
      assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hin & _ & Hrr); exists sg; split; assumption).
      rewrite SKEEP; [exact (HROM a Hrom) | exact (SIMGr a Hi) | exact (SIMG a Hi)]. }
    assert (SGBUF : garr8 SEGS (arm W1 (ms_mem ms)) (re_buf e1) (bzs (re_U e1 ++ re_junk e1))).
    { apply (akept_garr8 W1 m1 W1 (ms_mem ms)); [|exact Hgbuf].
      intros x Hx. rewrite la_len_bzs, length_app in Hx.
      apply (SKBLK (re_buf e1, re_cap e1) x);
        [ exact (proj1 (SINe _ ltac:(unfold aentry_blks; apply in_or_app; left;
            destruct (Z.eqb_spec (re_cap e1) 0); [lia|]; left; reflexivity)))
        | exact (proj2 (SINe _ ltac:(unfold aentry_blks; apply in_or_app; left;
            destruct (Z.eqb_spec (re_cap e1) 0); [lia|]; left; reflexivity)))
        | cbn [fst snd]; rewrite RQB; clear - Hx HUlen Hjunk Husedr; lia ]. }
    assert (SKOUT : akept W1 m1 W1 (ms_mem ms)
      (aout_fp B RG (drain_b_c.ds_ocap
         (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) out1)).
    { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & Hblk).
      set (OC := drain_b_c.ds_ocap
        (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) in *.
      intros r Hr a Ha. unfold aout_fp in Hr. cbn [In] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
        cbn [fst snd] in Ha.
      - apply SKIMG. apply SGOimg. unfold inG. apply Exists_exists.
        exists (rg_send_max RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKIMG. apply SGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (rg_nout RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKIMG. apply SGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (rg_capout RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKIMG. apply SGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (rg_out RG, 8). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKIMG. apply SGOimg. unfold inG. apply Exists_exists.
        exists (rg_client RG, 4). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKIMG. apply SGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (rg_client_broken RG, 1). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKIMG. apply SGOimg. unfold inG. apply Exists_exists.
        exists (rg_send_dead RG, 1). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKIMG. apply SGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (rg_send_eintr RG, 1). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - apply SKIMG. apply SGimg. unfold inG, G_DR, G_SL. apply Exists_exists.
        exists (as_errno B, 4). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - destruct (Z.eqb_spec OC 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
        destruct Hr as [<- | []]. cbn [fst snd] in Ha.
        destruct Hblk as [(Hcz & _)|(_ & _ & Hin & _)]; [exfalso; exact (Hc0 Hcz)|].
        assert (Hrq : req_size OC = OC)
          by (unfold req_size; destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia | reflexivity]).
        apply (SKBLK (out1, OC) a);
          [ exact (proj1 (SINo _ ltac:(unfold aout_blks;
              destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia|]; left; reflexivity)))
          | exact (proj2 (SINo _ ltac:(unfold aout_blks;
              destruct (Z.eqb_spec OC 0) as [Hz|Hz]; [lia|]; left; reflexivity)))
          | cbn [fst snd]; rewrite Hrq; lia ]. }
    assert (SOUT : aout_at B RG ly1 S1 W1 (ms_mem ms)
      (dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D ++ drlp s1 p)))) ev1)
      (if dlive cx then dxO cx ++ LB1 else dxO cx) (dxmx cx)
      (if dlive cx then dlno s1 p else dxno cx)
      (drain_b_c.ds_ocap
         (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) out1).
    { exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 (ms_mem ms) _ _ _ _ _ out1 HOUT SKOUT
        ltac:(intros bn Hbn; exact (proj1 (SINo bn Hbn)))). }
    set (SLC := dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D ++ drlp s1 p)))) ev1) in *.
    set (SLO := if dlive cx then dxO cx ++ LB1 else dxO cx) in *.
    set (SLN := if dlive cx then dlno s1 p else dxno cx) in *.
    set (SLOC := drain_b_c.ds_ocap
      (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))) in *.
    set (SLB := firstn (q - p + 1) (skipn p (re_U e1))) in *.
    (* The owed trace splits at this send, so dbud's three bounds give send_line's three premises. *)
    assert (HLEQ : Z.of_nat (length SLB) = Z.of_nat (length (dline s1 p q)) + 1)
      by (rewrite HBLL, (la_dline_len s1 p q Hpq); clear - Hpq; lia).
    assert (HSLIVE : sl_live SLC (Z.of_nat (length SLB)) = dlive cx).
    { unfold SLC. apply la_live_bridge_x; [|exact DRTOT].
      rewrite HBLL. clear - Hpq. lia. }
    assert (STRNIL : forall mx no cap len j o,
      send_line_b_c.send_line_tr false mx no cap len j o = []) by reflexivity.
    destruct (la_drl_send s1 p q Hbnd Hpq Hnulq Hnoq LASK HLL) as (ESEND1 & ESEND2).
    rewrite ESEND2 in Hfut.
    destruct (la_dlfut_cons cx (dnext (dlive cx) (dxmx cx) s1) aa (dlno s1 p) (dloc cx s1 p)
      (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) (drlq s1 (S q)) jb oo ha ks tl Hfut)
      as (tlR & HTL & HSF).
    pose proof HDLC as HDLCc. apply la_cut_facts_xR in HDLCc.
    destruct HDLCc as (HU0 & Hcap0 & Hmx0 & Hno0 & Hoc0 & Hka0 & Hen0 & Hec0).
    pose proof HDLC as HDLCd.
    eapply la_cut_dnext_signs_xR in HDLCd;
      [| exact Hmx0 | exact Hbnd | reflexivity | reflexivity | intros Hx; exact Hx].
    destruct HDLCd as (Soc & Sc & So & Sn & Se & Sec & Sk).
    assert (HSZ : tr_sizes_ok tl)
      by (exact (gs_dlfut_sizes cx (dnext (dlive cx) (dxmx cx) s1) aa (dlno s1 p) (dloc cx s1 p)
                   (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q :: drlq s1 (S q)) jb oo ha ks tl
                   Hmx0 Soc Sc So Sn Se Sec Sk Hfut)).
    pose proof HBUD as ((HBmo & HBsp & HBcost & HBalloc & HBmax) & HBRM & HBCNT).
    rewrite HTL in HSZ, HBcost, HBalloc, HBmax, HBRM, HBCNT.
    destruct (gs_tr_sizes_app _ _ HSZ) as (HSZ1 & HSZ2).
    rewrite (dr_tr_cost_app MT) in HBcost.
    rewrite dr_tr_max_app in HBmax.
    pose proof (gs_tr_cost_nonneg MT MTL _ HSZ1) as HC1.
    pose proof (gs_tr_cost_nonneg MT MTL _ HSZ2) as HC2.
    (* the PROGRAM CALL at 0x839f0: send_line (s->buf + p, q - p + 1) *)
    eapply (YA0nH.SRrG_bind SEGS R R_trans).
    { eapply (gx_callS_xR SEGS B PST ARx LAWS pa_segs_low R_trans (G_DR B RG) W1 (ms_regs ms) (ms_mem ms) _
        DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpn (dxW cx) (dxmem cx) (dxmd cx) []
        ly1 S1 Hp1 _ _ SL_STK (ablocks_fp (aout_blks SLOC out1)) (- DRAIN_FRAME)
        (Z_to_bv 64 (BASE + A_dr_send)) []
        (fun ly2 S2 Hp2 W2 regs2 mem2 md2 => exists out2,
           (* the callee's OWN journal, at G_SL: it is what says the harness source in g_s - which is in
              G_DR but not in G_SL - comes through the call unchanged *)
           (exists kk mdk, @ajournal_gx_xR _ SK SEGS B PST ARx R (G_SL B RG) 0 [] SL_STK (spZ (ms_regs ms))
              (ablocks_fp (aout_blks SLOC out1)) ly1 S1 Hp1 W1 (ms_mem ms) mdk [] ly2 S2 Hp2 W2 mem2 md2 kk) /\
           apres_kept B W1 (ms_mem ms) W2 mem2 /\
           mo_le MT S1 S2 (sl_cost MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB))) /\
           (* the room the rest of the owed trace needs, handed back by send_line's post *)
           rp_RM RP S2 (Z.to_nat (tr_cost MT_rk tlR) + kr) /\
           (exists rest, Permutation (ablocks B ly1 S1) (aout_blks SLOC out1 ++ rest) /\
              Permutation (ablocks B ly2 S2)
                (aout_blks (sl_cap SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB))) out2 ++ rest)) /\
           aout_at B RG ly2 S2 W2 mem2 (sl_ctl SLC (Z.of_nat (length SLB)))
             (sl_O SLC SLO SLB) (dxmx cx) (sl_no SLC SLN (Z.of_nat (length SLB)))
             (sl_cap SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB))) out2 /\
           (sl_live SLC (Z.of_nat (length SLB)) = false -> out2 = out1))
        HG HJ).
      - unfold spZ. rewrite S2r, Usp. lia.
      - vm_compute. reflexivity.
      - unfold DRAIN_FRAME. lia.
      - unfold SL_STK, SL_FRAME, ASTACK. lia.
      - unfold DRAIN_STK_x, DRAIN_STK, SL_STK, SL_FRAME, ASTACK, DRAIN_FRAME. lia.
      - rewrite S3r, (EE 3%nat 3%bv eq_refl), Hr3. exact Hgp.
      - rewrite S4r, (EE 4%nat 4%bv eq_refl), Hr4. exact Htp.
      - exact S1r.
      - apply (ret_ok_codeptr_v A_dr_send); rewrite HADS; [lia | reflexivity].
      - rewrite la_u64 by (rewrite HADS; lia). rewrite HADS. lia.
      - apply achain_low. unfold s0Z. rewrite S8r, (EE 8%nat 8%bv eq_refl), Hr8.
        rewrite la_u64 by (clear - HGSB0; unfold ASRC in *; lia).
        clear - HGSB0 C1. unfold ASRC in *. lia.
      - (* send_line's contract *)
        intros HPRE. eapply YA0nH.SRrG_mono.
        { (* sl_spec_x at the budget kr' = what the rest tlR of the owed trace charges, plus the entry's kr *)
          refine (SLSPEC_R W1 ly1 S1 Hp1 (ms_regs ms) (ms_mem ms) _ [] SLC SLO (dxmx cx) SLN SLOC out1
            (re_buf e1 + Z.of_nat p) SLB HPRE _ _ _ _ _ _ _ _ _ _ _ _ (Z.to_nat (tr_cost MT_rk tlR) + kr)%nat _ _).
          - rewrite S10, E33. reflexivity.
          - rewrite S11,
              (la_len_bv (ew E 33) (ew E 34) (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat q)
                 U33 U34 ltac:(lia) ltac:(lia) ltac:(lia)).
            rewrite HBLL. f_equal. clear - Hpq. lia.
          - exact SOUT.
          - exact SROM.
          - (* the line's bytes are a window of the relay buffer's *)
            replace (bzs SLB)
              with (firstn (q - p + 1) (skipn p (bzs (re_U e1 ++ re_junk e1)))).
            2:{ unfold SLB. rewrite la_bzs_app,
                  (la_fs_app (bzs (re_U e1)) (bzs (re_junk e1)) p (q - p + 1)
                     ltac:(rewrite la_len_bzs; clear - Hpq HUL; lia)).
                rewrite la_bzs_firstn, la_bzs_skipn. reflexivity. }
            apply (la_garr8_sub W1 (ms_mem ms) (re_buf e1) _ p (q - p + 1) SGBUF).
            rewrite la_len_bzs, length_app. clear - Hpq HUL. lia.
          - clear - HBP1. lia.
          - rewrite HBLL. clear - HBQ2 HBP1 Hpq. lia.
          - (* the line sits in the relay buffer, which is not g_out's block *)
            right. left. exists (re_buf e1), (re_cap e1).
            split; [exact Hbufin|]. split; [exact HBUFO|].
            split; [clear; lia|]. rewrite RQB, HBLL. clear - Hpq HUL Hdwlen Husedr. lia.
          - (* the line is in a live block, so none of its bytes is an image byte *)
            intros a Ha HinG.
            refine (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) a HAR Hbufin _ _).
            + rewrite RQB. rewrite HBLL in Ha. clear - Ha Hpq HUL Hdwlen Husedr. lia.
            + refine (proj1 (HG a _)). unfold inG, G_DR. apply Exists_cons_tl. exact HinG.
          - (* the request bound: the send's largest request is one of the owed trace's *)
            rewrite <- (dr_sl_tr_max_c SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) jb oo), HSLIVE.
            destruct (dlive cx) eqn:HLV.
            + replace SLN with (dlno s1 p) by (unfold SLN; reflexivity).
              replace SLOC with (dloc cx s1 p) by (unfold SLOC; reflexivity).
              rewrite HLEQ. clear - HBmax. lia.
            + rewrite STRNIL. cbn [tr_max fold_right]. clear - HMMAX. lia.
          - (* the live bytes (C3): the send's requests open the trace still owed, so their peak is within that
               trace's (W_tr_peak.v sl_peak_callee) *)
            unfold sl_tr. rewrite HSLIVE.
            destruct (dlive cx) eqn:HLV.
            + replace SLN with (dlno s1 p) by (unfold SLN; reflexivity).
              replace SLOC with (dloc cx s1 p) by (unfold SLOC; reflexivity).
              rewrite HLEQ.
              exact (W_tr_peak.sl_peak_callee [] tlR (blocks_bytes S1) (blocks_bytes S1) true (dxmx cx) (dlno s1 p)
                (dloc cx s1 p) (Z.of_nat (length (dline s1 p q)) + 1) jb oo LIVE_MAX
                ltac:(unfold tr_net; cbn [fold_right]; lia) HBalloc).
            + rewrite STRNIL in HBalloc |- *. cbn [app] in HBalloc.
              pose proof (W_tr_peak.tr_peak_nonneg tlR) as HPk0.
              rewrite W_tr_peak.tr_peak_nil. clear - HBalloc HPk0. lia.
          - (* the meter: the send's cost is the first part of the owed trace's *)
            pose proof HB as HBb. unfold DBASE_x in HBb.
            destruct HBb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
              & _ & _ & _ & HMOK & _).
            refine (mok_station MT (dxS cx) S1 _ spent _ MTL HMOK HBmo _ _).
            + rewrite <- (dr_sl_tr_cost_c MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) jb oo), HSLIVE.
              destruct (dlive cx) eqn:HLV.
              * replace SLN with (dlno s1 p) by (unfold SLN; reflexivity).
                replace SLOC with (dloc cx s1 p) by (unfold SLOC; reflexivity).
                rewrite HLEQ. clear - HC1. lia.
              * rewrite STRNIL. cbn [tr_cost fold_right]. clear. lia.
            + rewrite <- (dr_sl_tr_cost_c MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) jb oo), HSLIVE.
              destruct (dlive cx) eqn:HLV.
              * replace SLN with (dlno s1 p) by (unfold SLN; reflexivity).
                replace SLOC with (dloc cx s1 p) by (unfold SLOC; reflexivity).
                rewrite HLEQ. clear - HBcost HC2. lia.
              * rewrite STRNIL in HBcost |- *. cbn [tr_cost fold_right] in HBcost |- *.
                clear - HBcost HC2. lia.
          - (* THE ROOM (an internal work row; W_drain_room_x.v gs_rm_take): the cut's room is MT_rk's charge of the owed trace on
               top of kr; the send's requests open that trace and their charge is send_line's sl_cost at MT_rk, so the
               budget kr' the post hands back is the rest's charge plus kr *)
            refine (gs_rm_take RP S1 _ tlR kr _ _ HBRM).
            rewrite <- (dr_sl_tr_cost_c MT_rk SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) jb oo), HSLIVE.
            destruct (dlive cx) eqn:HLV.
            + replace SLN with (dlno s1 p) by (unfold SLN; reflexivity).
              replace SLOC with (dloc cx s1 p) by (unfold SLOC; reflexivity).
              rewrite HLEQ. lia.
            + rewrite !STRNIL. lia.
          - (* THE COUNTS (an internal work row): send_line's count peak sl_pk = 2 is the + 2 of the cut's count shape *)
            eapply cnt_ok_pk_mono; [|exact HBCNT].
            intros P. cbv [sl_pk]. lia. }
        cbv beta.
        intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & out2 & -> & HJ2 & HPRs & HAK2 & HMO2 & HRM2
          & HPm2 & HO2 & HOFF2).
        exists ly2, S2, Hp2, regs2, mem2, md2, k2.
        split; [rewrite S1r, HADS; reflexivity|].
        split; [eapply ajournal_gx_G_mono_xR;
                [intros a Ha; unfold inG, G_DR; apply Exists_cons_tl; exact Ha | exact HJ2]|].
        split; [exact HPRs|].
        exists out2. split; [exists k2; eexists; exact HJ2|].
        split; [exact HAK2|]. split; [exact HMO2|]. split; [exact HRM2|]. split; [exact HPm2|].
        split; [exact HO2 | exact HOFF2].
      - (* The callee's footprint is the CURRENT g_out block, the journal's (dFP cx, W_contract.v:815) the
           ENTRY's.  A g_out block that is not one of the entry's blocks is a tmp block (YCbq.v:344).  One
           that is, is by DBASE's entry permutation the table block or a dxrest block - both impossible,
           since the current permutation lists them apart from g_out and ablocks has no duplicate - or an
           entry / source / g_out block of the entry, all of which dFP covers. *)
        intros a Ha. apply inFP_ablocks_fp_inv in Ha. destruct Ha as (pb & nb & Hin & Hpa).
        assert (HinC : In (pb, nb) (ablocks B ly1 S1)).
        { apply (Permutation_in _ (Permutation_sym HPERM)). right.
          apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (DEC : forall x y : Z * Z, {x = y} + {x <> y}).
        { intros [x1 x2] [y1 y2]. destruct (Z.eq_dec x1 y1) as [->|N1]; [|right; congruence].
          destruct (Z.eq_dec x2 y2) as [->|N2]; [left; reflexivity | right; congruence]. }
        destruct (in_dec DEC (pb, nb) (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hin0].
        2:{ right. exists pb, nb. split; [exact HinC|]. split; [exact Hin0 | exact Hpa]. }
        left. split; [| exists pb, nb; split; [exact HinC | exact Hpa]].
        pose proof HB as HB0. unfold DBASE_x in HB0.
        destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPERM0 & _).
        apply (Permutation_in _ HPERM0) in Hin0.
        pose proof (Permutation_NoDup HPERM (la_ablocks_nodup_x ly1 S1 Hp1 W1 m1 md1 HAR)) as ND.
        assert (DFPIN : In (pb, nb) (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++
                                     aout_blks (dxcap cx) (dxout cx)) -> inFP (dFP cx) a).
        { intros HinE. unfold dFP, dr_fp. apply (proj2 (inFP_cons _ _ _ _)). right.
          pose proof (inFP_ablocks_fp _ pb nb (a - pb) HinE ltac:(clear - Hpa; lia)) as HI.
          replace (pb + (a - pb)) with a in HI by lia. exact HI. }
        destruct Hin0 as [Heq | Hin0].
        + (* the table block: it heads the current list, so it is not also g_out's *)
          exfalso. apply NoDup_cons_iff in ND. destruct ND as (Hni & _). apply Hni. rewrite Heq.
          apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin.
        + apply in_app_or in Hin0. destruct Hin0 as [Hin0|Hin0].
          { apply DFPIN. apply in_or_app. left. exact Hin0. }
          apply in_app_or in Hin0. destruct Hin0 as [Hin0|Hin0].
          { apply DFPIN. apply in_or_app. right. apply in_or_app. left. exact Hin0. }
          apply in_app_or in Hin0. destruct Hin0 as [Hin0|Hin0].
          { apply DFPIN. apply in_or_app. right. apply in_or_app. right. exact Hin0. }
          (* a dxrest block: the current list keeps dxrest apart from g_out *)
          exfalso. apply NoDup_cons_iff in ND. destruct ND as (_ & ND).
          apply la_nodup_app_r in ND. apply la_nodup_app_r in ND.
          exact (la_nodup_app_disj _ _ _ _ ND Hin Hin0). }
    (* back in drain after the send: build DLS and hand it to LINEB *)
    intros W3 c3 Hwle3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & Hc3 & HJ3 & HJc3 & HPR3 &
      out3 & HJSL0 & HAPK3 & HMO3 & HRM3 & HPRM3 & HO3 & HOFF3).
    destruct HJSL0 as (kSL & mdSL & HJSL).
    destruct HPRM3 as (rest3 & HPa3 & HPb3).
    apply (LINEB_R cx Hpn kr s1 D p q W3 c3 HB); [| exact HN | exact HGS].
    (* (1) the model: the line's bytes, with their NUL, are the send's argument (s->skip is 0: LASK) *)
    assert (HBSL : bzs SLB = dline s1 p q ++ [0]).
    { unfold SLB, dline. rewrite la_bzs_firstn, la_bzs_skipn, HUeq.
      replace (q - p + 1)%nat with (S (q - p)) by lia.
      apply la_firstn_S_x. rewrite la_nth_error_skipn_x.
      replace (p + (q - p))%nat with q by lia. exact Hnulq. }
    (* (2) the run from the branch to the call stored nothing: every byte is kept, s->skip's word too *)
    assert (SKALL : forall x, 0 <= x < 2 ^ 64 -> abyte_kept W1 m1 W1 (ms_mem ms) x).
    { intros x Hx.
      destruct (Z.ltb_spec x (dxSA cx + 8)); [apply SKEPT; [lia | exact Hx]|].
      destruct (Z.ltb_spec x (dxSA cx + 12)); [|apply SKEPT; [lia | exact Hx]].
      split; [|unfold arm; apply writable_kept; intros Hp; exact (SPRES x Hp)].
      set (kk := Z.to_nat (x - (dxSA cx + 8))).
      replace x with (dxSA cx + 8 + Z.of_nat kk) by (unfold kk; lia).
      pose proof LAVMs as LV. pose proof HSKV as HSK0. rewrite Hsk0 in HSK0. unfold arm in LV, HSK0.
      unfold aview. cbv beta.
      rewrite (LV kk ltac:(unfold kk; lia)), (HSK0 kk ltac:(unfold kk; lia)). reflexivity. }
    (* (3) what the call keeps: a byte off the image by its view, an image byte by apres_kept too *)
    assert (KNI : forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
      aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W1) (ms_mem ms) a ->
      abyte_kept W1 (ms_mem ms) W3 mem3 a).
    { intros a Hr Hni HV. split; [exact HV|]. unfold arm. apply la_wk2_x.
      intros Hh Hb. change (apresent (w_H W3) mem3 a).
      eapply apresent_transfer; [exact Hr | exact Hni | exact HV | exact (conj Hh Hb)]. }
    assert (KIM : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
      ~ (as_errno B <= a < as_errno B + 4) ->
      aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W1) (ms_mem ms) a ->
      abyte_kept W1 (ms_mem ms) W3 mem3 a).
    { intros a Hi Ho He HV. split; [exact HV|]. unfold arm. apply la_wk2_x.
      intros Hh Hb. exact (HAPK3 a Hi Ho He (conj Hh Hb)). }
    (* a block of S1 that is still a block of S3 and is not g_out's *)
    assert (CKB : forall bn a, In bn (ablocks B ly1 S1) -> In bn (ablocks B ly3 S3) ->
      ~ In bn (aout_blks SLOC out1) -> fst bn <= a < fst bn + req_size (snd bn) ->
      abyte_kept W1 (ms_mem ms) W3 mem3 a).
    { intros [b n] a Hin Hin3 Hno Ha. cbn [fst snd] in Ha.
      destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 b n HAR Hin) as (_ & Hb4 & Hbc & _).
      assert (Hni : ~ in_img SEGS a)
        by (intros Hi; exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 b n a HAR Hin ltac:(lia) Hi)).
      apply KNI; [lia | exact Hni|].
      replace a with (b + (a - b)) by lia.
      apply (la_keep_blk_xR (G_DR B RG) 0 [] SL_STK (dsp0 cx + - DRAIN_FRAME)
        (ablocks_fp (aout_blks SLOC out1)) ly1 S1 Hp1 W1 (ms_mem ms) _ [] ly3 S3 Hp3 W3 mem3 md3 k3
        HJc3 b n (a - b) Hin Hin3 ltac:(lia)).
      - intros Hfp. apply inFP_ablocks_fp_inv in Hfp. destruct Hfp as (pb & nb & Hinb & Hpa).
        assert (Hne : (b, n) <> (pb, nb)) by (intros Heq; rewrite Heq in Hno; exact (Hno Hinb)).
        pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 b n pb nb HAR Hin
          (proj1 (SINo (pb, nb) Hinb)) Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Ha Hpa. lia.
      - intros Hg. apply Hni. replace (b + (a - b)) with a in Hg by lia. exact (proj1 (HG a Hg)).
      - lia. }
    (* drain's own frame lies above send_line's window *)
    assert (CKF : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 (ms_mem ms) W3 mem3 x).
    { intros x Hx. apply KNI; [lia | |].
      - intros Hi. pose proof (Hsegs x Hi) as HL. unfold kLowMemEnd in HL. lia.
      - apply (la_keep_high_xR (G_DR B RG) 0 [] SL_STK (dsp0 cx + - DRAIN_FRAME)
          (ablocks_fp (aout_blks SLOC out1)) ly1 S1 Hp1 W1 (ms_mem ms) _ [] ly3 S3 Hp3 W3 mem3 md3 k3 HG HJc3 x);
          lia. }
    (* the g_s band: in G_DR, but not in G_SL, so send_line's OWN journal keeps it *)
    assert (CKG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 (ms_mem ms) W3 mem3 a).
    { intros a Ha.
      assert (HgD : inG (G_DR B RG) a).
      { unfold inG, G_DR. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
      destruct (HG a HgD) as (Hi & Ho & _).
      pose proof (la_zpw_x _ 2 4 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
      pose proof (la_zpw_x _ 2 5 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
      pose proof (la_zpw_x _ 2 8 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
      pose proof (la_zpw_x _ 2 9 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
      pose proof (la_zpw_x _ 2 10 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
      pose proof (la_zpw_x _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D11.
      cbn [nth] in D4, D5, D8, D9, D10, D11. unfold zdisj in D4, D5, D8, D9, D10, D11.
      cbn [fst snd] in D4, D5, D8, D9, D10, D11.
      assert (He : ~ (as_errno B <= a < as_errno B + 4)) by (intros He; clear - D11 Ha He; lia).
      apply KIM; [exact Hi | exact Ho | exact He|].
      (* the g_s band is no program static (PSTG), so the callee's journal keeps it like any image byte *)
      apply (la_keep_img_xR (G_SL B RG) 0 [] SL_STK (spZ (ms_regs ms))
        (ablocks_fp (aout_blks SLOC out1)) ly1 S1 Hp1 W1 (ms_mem ms) mdSL [] ly3 S3 Hp3 W3 mem3 md3 kSL HJSL
        a Hi Ho He (PSTG a Ha)).
      - apply la_fp_spares_blocks_x. intros [b n] Hbn.
        destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 b n HAR (proj1 (SINo (b, n) Hbn))) as (_ & H4 & _).
        exact H4.
      - intros Hg. unfold inG, G_SL in Hg. rewrite !Exists_cons, Exists_nil in Hg.
        unfold in_zr in Hg. cbn [fst snd] in Hg.
        destruct Hg as [Hg|[Hg|[Hg|[Hg|[Hg|[Hg|[]]]]]]].
        + clear - Hg Ha D4; lia.
        + clear - Hg Ha D5; lia.
        + clear - Hg Ha D8; lia.
        + clear - Hg Ha D9; lia.
        + clear - Hg Ha D10; lia.
        + clear - Hg Ha D11; lia. }
    (* (4) the composite keeps, from DLL's state through the call to the cut's *)
    assert (ABKT : forall (Wa : world SEGS) ma (Wb : world SEGS) mb (Wc : world SEGS) mc a,
      abyte_kept Wa ma Wb mb a -> abyte_kept Wb mb Wc mc a -> abyte_kept Wa ma Wc mc a).
    { intros Wa ma Wb mb Wc mc a (Hv1 & Hw1) (Hv2 & Hw2).
      split; [rewrite Hv2; exact Hv1 | intros Hh; exact (Hw2 (Hw1 Hh))]. }
    assert (KCF : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W1 m1 W3 mem3 x).
    { intros x Hx. apply (ABKT W1 m1 W1 (ms_mem ms)); [apply SKALL; lia | exact (CKF x Hx)]. }
    assert (KCGc : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W3 mem3 a).
    { intros a Ha. apply (ABKT W1 m1 W1 (ms_mem ms)); [apply SKALL; unfold ASRC in *; lia | exact (CKG a Ha)]. }
    (* the blocks at the cut: the call replaced g_out's block and kept the rest *)
    assert (SNOO : forall bn, In bn ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1) ->
      ~ In bn (aout_blks SLOC out1)).
    { intros bn Hin Hino.
      pose proof (Permutation_NoDup HPERM (la_ablocks_nodup_x ly1 S1 Hp1 W1 m1 md1 HAR)) as ND.
      rewrite app_assoc in ND.
      change ((dxG cx, ATABLE) :: (aentry_blks e1 ++ asrc_blks h1) ++ aout_blks SLOC out1 ++ dxrest cx)
        with (((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1) ++ (aout_blks SLOC out1 ++ dxrest cx))
        in ND.
      exact (la_nodup_app_disj _ _ _ bn ND Hin (in_or_app _ _ _ (or_introl Hino))). }
    assert (PR3 : Permutation rest3 ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ dxrest cx)).
    { apply (Permutation_app_inv_l (aout_blks SLOC out1)).
      eapply Permutation_trans; [apply Permutation_sym; exact HPa3|].
      eapply Permutation_trans; [exact HPERM|].
      eapply Permutation_trans; [|apply Permutation_middle].
      apply perm_skip. apply Permutation_sym.
      eapply Permutation_trans; [apply Permutation_app_swap_app|].
      apply Permutation_app_head. apply Permutation_app_swap_app. }
    assert (PERM3 : Permutation (ablocks B ly3 S3)
      ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++
         aout_blks (sl_cap SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB))) out3 ++ dxrest cx)).
    { eapply Permutation_trans; [exact HPb3|].
      eapply Permutation_trans; [apply Permutation_app_head; exact PR3|].
      eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
      apply perm_skip.
      eapply Permutation_trans; [apply Permutation_app_swap_app|].
      apply Permutation_app_head. apply Permutation_app_swap_app. }
    assert (SIN13 : forall bn, In bn ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1) ->
      In bn (ablocks B ly1 S1) /\ In bn (ablocks B ly3 S3)).
    { intros bn Hin. split.
      - apply (Permutation_in _ (Permutation_sym HPERM)).
        destruct Hin as [<-|Hin]; [left; reflexivity|right].
        rewrite app_assoc. apply in_or_app. left. exact Hin.
      - apply (Permutation_in _ (Permutation_sym PERM3)).
        destruct Hin as [<-|Hin]; [left; reflexivity|right].
        rewrite app_assoc. apply in_or_app. left. exact Hin. }
    assert (KCB : forall bn a, In bn ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1) ->
      fst bn <= a < fst bn + req_size (snd bn) -> abyte_kept W1 m1 W3 mem3 a).
    { intros bn a Hin Ha. destruct (SIN13 bn Hin) as (H1 & H3).
      apply (ABKT W1 m1 W1 (ms_mem ms)); [|exact (CKB bn a H1 H3 (SNOO bn Hin) Ha)].
      apply SKALL. destruct bn as [b n].
      destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 b n HAR H1) as (_ & Hb4 & Hbc & _).
      cbn [fst snd] in Ha. lia. }
    assert (KCE : forall b n a, In (b, n) (aentry_blks e1) -> b <= a < b + req_size n ->
      abyte_kept W1 m1 W3 mem3 a).
    { intros b n a Hin Ha. apply (KCB (b, n) a); [right; apply in_or_app; left; exact Hin | exact Ha]. }
    assert (KCS : forall bn a, In bn (asrc_blks h1) -> fst bn <= a < fst bn + req_size (snd bn) ->
      abyte_kept W1 m1 W3 mem3 a).
    { intros bn a Hin Ha. apply (KCB bn a); [right; apply in_or_app; right; exact Hin | exact Ha]. }
    (* the relay entry's footprint *)
    assert (KEN : akept W1 m1 W3 mem3 (aentry_fp e1)).
    { intros r Hr a Ha. unfold aentry_fp in Hr.
      destruct (Z.eqb_spec (re_cap e1) 0) as [Hc0|Hc0]; [lia|]. cbn [app In] in Hr.
      destruct Hr as [<- | [<- | Hr]].
      - unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, length_app in Ha.
        apply (KCE (re_buf e1) (re_cap e1) a); [|rewrite RQB; lia].
        unfold aentry_blks. apply in_or_app. left.
        destruct (Z.eqb_spec (re_cap e1) 0); [lia|]. left. reflexivity.
      - unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, la_key_ptrs_len in Ha.
        pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hheld & _).
        destruct Hheld as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
        + exfalso. rewrite Hke in Ha. cbn [length] in Ha. lia.
        + pose proof (BLKN ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as Hn0.
          pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (_ & Hrq).
          unfold re_nheld in Hk1.
          apply (KCE (re_hp e1) (re_kh e1) a); [|lia].
          unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
          destruct (Z.eqb_spec (re_hp e1) 0); [lia|]. left. reflexivity.
      - apply in_map_iff in Hr. destruct Hr as (kk & Hre & Hkk). subst r.
        unfold gfp in Ha. cbn [fst snd] in Ha.
        rewrite la_len_bzs, length_app in Ha. cbn [length] in Ha.
        pose proof HEOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkeys).
        rewrite Forall_forall in Hkeys. destruct (Hkeys kk Hkk) as (Hin & _ & _ & Hlen).
        pose proof (req_size_pos (Z.of_nat (length (key_text kk)) + 1) ltac:(lia)) as (_ & Hrq).
        apply (KCE (key_addr kk) (Z.of_nat (length (key_text kk)) + 1) a); [|lia].
        unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
        apply in_map_iff. exists kk. split; [reflexivity | exact Hkk]. }
    (* the harness source's footprint *)
    assert (KLIST : forall LA l lines0,
      alist_at B ly1 S1 W1 m1 LA l lines0 ->
      (forall x, LA <= x < LA + 16 -> abyte_kept W1 m1 W3 mem3 x) ->
      (forall bn, In bn (alist_blks l) -> In bn (asrc_blks h1)) ->
      akept W1 m1 W3 mem3 (alist_fp LA l)).
    { intros LA l lines0 HL HLA HB2 r Hr a Ha.
      pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
      unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
      - cbn [fst snd] in Ha. exact (HLA a Ha).
      - apply in_app_or in Hr. destruct Hr as [Hr|Hr].
        + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
          destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
          rewrite la_len_bzs, length_app, la_recs_len in Ha.
          destruct Hv as [(Hcz & _)|(_ & Hin & Hj & _)]; [lia|].
          unfold hl_n in *. unfold AREC in *.
          pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
          unfold AREC in Hrq.
          apply (KCS (hl_v l, AREC * hl_cap l) a);
            [ exact (HB2 _ ltac:(unfold alist_blks; apply in_or_app; left;
                destruct (Z.eqb_spec (hl_cap l) 0); [lia|]; left; reflexivity))
            | cbn [fst snd]; unfold AREC; lia ].
        + apply in_map_iff in Hr. destruct Hr as (rr & Hre & Hrr). subst r.
          unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs, length_app in Ha. cbn [length] in Ha.
          rewrite Forall_forall in Hrecs. destruct (Hrecs rr Hrr) as (Hin & _).
          pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as (_ & Hrq).
          apply (KCS (fst rr, Z.of_nat (length (snd rr)) + 1) a);
            [ exact (HB2 _ ltac:(unfold alist_blks; apply in_or_app; right;
                apply in_map_iff; exists rr; split; [reflexivity | exact Hrr]))
            | cbn [fst snd]; lia ]. }
    assert (KSRC : akept W1 m1 W3 mem3 (asrc_fp (dHA RG cx) h1)).
    { pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj
        & _ & _ & Hexp & Hhld & _).
      intros r Hr a Ha. unfold asrc_fp in Hr. cbn [In] in Hr.
      destruct Hr as [<- | [<- | Hr]].
      - cbn [fst snd] in Ha. apply KCGc. unfold dHA in *. unfold ASRC in *. lia.
      - unfold gfp in Ha. cbn [fst snd] in Ha. rewrite la_len_bzs in Ha.
        pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
        apply (KCS (hs_partial h1, APARTIAL) a); [left; reflexivity | cbn [fst snd]; lia].
      - apply in_app_or in Hr. destruct Hr as [Hr|Hr].
        + apply (KLIST (dHA RG cx + 16) (hs_pending h1) _ Hpend
            ltac:(intros x Hx; apply KCGc; unfold dHA in *; unfold ASRC in *; lia)
            ltac:(intros bn Hbn; right; apply in_or_app; left; exact Hbn) r Hr a Ha).
        + apply in_app_or in Hr. destruct Hr as [Hr|Hr].
          * apply (KLIST (dHA RG cx + 64) (hs_expected h1) _ Hexp
              ltac:(intros x Hx; apply KCGc; unfold dHA in *; unfold ASRC in *; lia)
              ltac:(intros bn Hbn; right; apply in_or_app; right; apply in_or_app; left; exact Hbn)
              r Hr a Ha).
          * apply (KLIST (dHA RG cx + 80) (hs_held h1) _ Hhld
              ltac:(intros x Hx; apply KCGc; unfold dHA in *; unfold ASRC in *; lia)
              ltac:(intros bn Hbn; right; apply in_or_app; right; apply in_or_app; right; exact Hbn)
              r Hr a Ha). }
    (* (5) the registers: send_line keeps the callee-saved ones *)
    assert (PRr : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr (ms_regs ms) r).
    { intros r Hr. pose proof (HPR3 (bv_unsigned r) Hr) as Er. rewrite Z_to_bv_bv_unsigned in Er. exact Er. }
    assert (DR3 : dregs_line RG cx regs3 W3 mem3).
    { apply (la_dregs_kept_x cx regs1 regs3 W1 m1 W3 mem3 Hregs); [| | | | | | | | | | exact KCF].
      - rewrite (PRr 2%bv ltac:(la_cs_x)), S2r. exact (EE 2%nat 2%bv eq_refl).
      - rewrite (PRr 3%bv ltac:(la_cs_x)), S3r. exact (EE 3%nat 3%bv eq_refl).
      - rewrite (PRr 4%bv ltac:(la_cs_x)), S4r. exact (EE 4%nat 4%bv eq_refl).
      - rewrite (PRr 21%bv ltac:(la_cs_x)), S21r. exact (EE 21%nat 21%bv eq_refl).
      - rewrite (PRr 20%bv ltac:(la_cs_x)), S20r. exact (EE 20%nat 20%bv eq_refl).
      - rewrite (PRr 22%bv ltac:(la_cs_x)), S22r. exact (EE 22%nat 22%bv eq_refl).
      - rewrite (PRr 27%bv ltac:(la_cs_x)), S27r. exact (EE 27%nat 27%bv eq_refl).
      - rewrite (PRr 8%bv ltac:(la_cs_x)), S8r. exact (EE 8%nat 8%bv eq_refl).
      - rewrite (PRr 9%bv ltac:(la_cs_x)), S9r. exact (EE 9%nat 9%bv eq_refl).
      - rewrite (PRr 18%bv ltac:(la_cs_x)), S18r. exact (EE 18%nat 18%bv eq_refl). }
    (* (6) the model at the cut: the send's controller, output, count, capacity and meter *)
    assert (HWN1 : with_nul (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) =
      with_nul (lines (dSTR cx) D ++ drlp s1 p) ++ (dline s1 p q ++ [0])).
    { rewrite app_assoc. unfold with_nul. rewrite map_app, concat_app. cbn [map concat].
      rewrite app_nil_r. reflexivity. }
    destruct (la_ctl_step_x cx (Z.of_nat (length (with_nul (lines (dSTR cx) D ++ drlp s1 p)))) ev1
      (Z.of_nat (length SLB)) ltac:(lia) ltac:(lia)) as (ev3 & Hev3).
    assert (ECTL : sl_ctl SLC (Z.of_nat (length SLB)) =
      dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])))) ev3).
    { transitivity (dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D ++ drlp s1 p))) +
        Z.of_nat (length SLB)) ev3); [exact Hev3|].
      f_equal. rewrite HWN1, length_app, length_app. cbn [length]. rewrite HLEQ. lia. }
    assert (ESLO : sl_O SLC SLO SLB = (if dlive cx then dxO cx ++ (LB1 ++ SLB) else dxO cx)).
    { unfold sl_O. rewrite HSLIVE. unfold SLO.
      destruct (dlive cx); [rewrite <- app_assoc; reflexivity | reflexivity]. }
    assert (ESNO : sl_no SLC SLN (Z.of_nat (length SLB)) =
      (if dlive cx then dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1 else dxno cx)).
    { unfold sl_no. rewrite HSLIVE. unfold SLN. destruct (dlive cx); [rewrite HLEQ; ring | reflexivity]. }
    assert (ECAP : sl_cap SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) =
      send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
        (Z.of_nat (length (dline s1 p q)) + 1)).
    { unfold sl_cap. rewrite HSLIVE, HLEQ. unfold SLN.
      replace SLOC with (dloc cx s1 p) by reflexivity.
      destruct (dlive cx); reflexivity. }
    assert (ESC : sl_cost MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) =
      tr_cost MT (send_line_b_c.send_line_tr (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
        (Z.of_nat (length (dline s1 p q)) + 1) jb oo)).
    { rewrite <- (dr_sl_tr_cost_c MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) jb oo), HSLIVE.
      destruct (dlive cx) eqn:HLV.
      - replace SLN with (dlno s1 p) by (unfold SLN; reflexivity).
        replace SLOC with (dloc cx s1 p) by (unfold SLOC; reflexivity). rewrite HLEQ. reflexivity.
      - rewrite !STRNIL. reflexivity. }
    assert (HSLOC0 : 0 <= SLOC).
    { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & Hblk).
      destruct Hblk as [(Hz & _)|(Hz & _)]; lia. }
    (* (7) DLS *)
    unfold DLS_xR.
    exists regs3, ly3, S3, Hp3, mem3, md3, (k1 + k3), e1, h1, out3, ev3, (LB1 ++ SLB),
      (spent + sl_cost MT SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB))).
    eexists. exists aa. eexists. exists ha, ks, tlR.
    split; [rewrite Hc3; reflexivity|].
    split; [exact DR3|].
    split; [rewrite (PRr 23%bv ltac:(la_cs_x)), S23r, E34; reflexivity|].
    split; [rewrite (PRr 24%bv ltac:(la_cs_x)), S24r, E33; reflexivity|].
    split; [exact Hdib|]. split; [exact Hcapp|].
    split; [exact Hbnd|]. split; [exact Hpq|]. split; [exact Hnulq|]. split; [exact Hnoq|].
    split; [exact LASK|]. split; [exact HLL|].
    split.
    2:{ replace (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
          with (dlno s1 p + (Z.of_nat (length (dline s1 p q)) + 1)) by ring.
        exact HSF. }
    unfold LCORE_xR. cbv zeta.
    split.
    { unfold DMEM_xR.
      split; [exact HJ3|].
      split; [eapply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS Hsegs); [exact HJc3 | exact HROMO | exact PSTR | exact SROM]|].
      split.
      { apply (la_apk_trans_x (dxW cx) (dxmem cx) W1 (ms_mem ms) W3 mem3); [|exact HAPK3].
        apply (la_apk_trans_x (dxW cx) (dxmem cx) W1 m1 W1 (ms_mem ms)); [exact HPRES|].
        intros a Hi Ho He Hp. exact (SPRES a Hp). }
      split; [rewrite (la_gx_frames_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3); exact HFRAMES|].
      split; [exact (la_frame_kept_x cx W1 m1 W3 mem3 KCF HFR2)|].
      split.
      { apply (akept_garr8 W1 m1 W3 mem3); [|exact HGARR].
        intros x Hx. rewrite la_len_bzs, HEBL in Hx.
        apply (KCB (dxG cx, ATABLE) x); [left; reflexivity | cbn [fst snd]; rewrite RQT; lia]. }
      split.
      { apply (akept_awr W1 m1 W3 mem3); [|exact HAWR].
        intros x Hx. apply (KCB (dxG cx, ATABLE) x);
          [left; reflexivity | cbn [fst snd]; rewrite RQT; unfold AENT in *; lia]. }
      split.
      { apply (la_aentry_okx_kept_x ly1 S1 W1 m1 ly3 S3 W3 mem3 e1 HEOK KEN).
        intros bn Hbn. exact (proj2 (SIN13 bn ltac:(right; apply in_or_app; left; exact Hbn))). }
      split.
      { apply (asrc_at_kept B ly1 S1 W1 m1 ly3 S3 W3 mem3 (dHA RG cx) h1 HSRC KSRC).
        intros bn Hbn. exact (proj2 (SIN13 bn ltac:(right; apply in_or_app; right; exact Hbn))). }
      split.
      { intros i Hi Hne. destruct (HOTH i Hi Hne) as (f & o & V1 & V2 & Hd).
        exists f, o. split.
        { eapply akept_vm; [intros x Hx; apply KCGc; unfold ASRC in *; lia | exact V1]. }
        split; [|exact Hd].
        eapply akept_vm; [intros x Hx; apply KCGc; unfold ASRC in *; lia | exact V2]. }
      split.
      { intros x Hx Hnx. apply (ABKT (dxW cx) (dxmem cx) W1 m1 W3 mem3 x);
          [exact (HKEPT x Hx Hnx) | exact (KCGc x Hx)]. }
      split.
      { rewrite ECTL, ESLO, ESNO, ECAP in HO3. exact HO3. }
      split.
      { intros HLf. destruct (HLIVE HLf) as (Ho1 & Hcx1). split.
        - rewrite <- Ho1. apply HOFF3. rewrite HSLIVE. exact HLf.
        - unfold dvirt. cbv zeta. cbn [drain_b_c.ds_ocap]. rewrite HLf. exact Hcx1. }
      rewrite ECAP in PERM3. exact PERM3. }
    split.
    { pose proof HLINK as HL0. unfold DLINK in HL0 |- *.
      destruct HL0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
      split; [exact L1|]. split; [exact L2|]. split; [exact Hsk0|].
      split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|].
      split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact L11|]. exact L12. }
    split; [exact HSAME|].
    split.
    { pose proof HHIST as HH0. unfold DHIST in HH0 |- *.
      destruct HH0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
      split.
      { cbn [dvirt drain_b_c.ds_no] in H6 |- *.
        rewrite HWN1, length_app, length_app. cbn [length]. lia. }
      split; [rewrite la_bzs_app, H7, HBSL, HWN1; reflexivity|].
      split; [exact H8|]. split; [exact H9|].
      split; [|exact H11].
      replace (Z.of_nat (S (length (drlq s1 (S q))))) with (Z.of_nat (length (drlq s1 p)))
        by (rewrite ESEND2; reflexivity).
      exact H10. }
    split; [exact HRST|].
    (* dbud_x at the cut: W_drain_cx.v's dbud, the room, the counts *)
    split; [split; [|split; [|split; [|split]]] | split].
    * exact (mo_le_trans MT MTL _ _ _ _ _ HBmo HMO3).
    * rewrite ESC. clear - HBsp HC1. lia.
    * rewrite ESC. clear - HBcost. lia.
    * (* C3: the send moves g_out's capacity from SLOC to sl_cap, exactly its requests' net change (W_tr_peak.v
         send_line_tr_net), so the peak of the rest stays in room (tr_peak_app) *)
      rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPb3), bsum_app.
      pose proof (sl_maxr_le_cap SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB)) HSLOC0) as (HM0 & HM1).
      rewrite la_bsum_out_x by lia.
      rewrite (blocks_bytes_bsum B ly1 S1), (bsum_perm _ _ HPa3), bsum_app, (la_bsum_out_x SLOC out1 HSLOC0)
        in HBalloc.
      rewrite (W_tr_peak.tr_peak_app _ tlR), W_tr_peak.send_line_tr_net in HBalloc.
      rewrite ECAP. replace SLOC with (dloc cx s1 p) in HBalloc by reflexivity. clear - HBalloc. lia.
    * clear - HBmax. lia.
    * (* THE ROOM (an internal work row): send_line's post hands back exactly the budget the rest tlR needs *)
      exact HRM3.
    * (* THE COUNTS (an internal work row; W_drain_room_x.v gs_cnt_step): the send moves g_out's block from SLOC to sl_cap,
         exactly its requests' net count change (la_sl_tr_cnt), so the rest's count peak stays under the bounds
         (tr_peak_w_app) *)
      refine (gs_cnt_step RP _ tlR _ _ _ HBCNT).
      intros P.
      rewrite (acnt_perm P _ _ HPb3), (acnt_perm P _ _ HPa3), !acnt_app.
      assert (A1 : Z.of_nat (acnt P (aout_blks SLOC out1)) = la_oc P (dloc cx s1 p))
        by exact (la_acnt_out P SLOC out1).
      assert (A3 : Z.of_nat (acnt P (aout_blks (sl_cap SLC (dxmx cx) SLN SLOC (Z.of_nat (length SLB))) out3)) =
        la_oc P (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
          (Z.of_nat (length (dline s1 p q)) + 1)))
        by (rewrite <- ECAP; apply la_acnt_out).
      pose proof (la_sl_tr_cnt P (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
        (Z.of_nat (length (dline s1 p q)) + 1) jb oo HSLOC0) as NET.
      rewrite !tr_peakP_w, ReplyTrPeakW.tr_peak_w_app.
      pose proof (ReplyTrPeakW.tr_peak_w_nonneg (fun n => zb (P n))
        (send_line_b_c.send_line_tr (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
          (Z.of_nat (length (dline s1 p q)) + 1) jb oo)) as PK1.
      clear - A1 A3 NET PK1. lia.
  + (* not taken: 6001 <= nul - start, so the line is overlong and only s->skip is cleared *)
    rewrite branch_ltu_U in Hc.
    rewrite (la_U_diff E 33%nat 34%nat _ _ U33 U34 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
    rewrite U_SLit in Hc. change (zcanon 6001) with 6001 in Hc.
    apply Z.ltb_ge in Hc.
    paj_run_to_tok_xR RUNTOR HS HJ SHOK la_Bspan A_dr_next.
    { unfold ss_la, la_regions, la_fr, la_ent. cbn [ss_mem].
      apply awr_ok_x_cons.
      - cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. intros a Ha. exfalso. clear - Ha. lia.
      - apply awr_ok_x_cons; [|apply awr_ok_x_nil].
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. rewrite BV32. intros a Ha.
        left. split; [|lia]. right. left. split.
        + unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
          cbn [fst snd]. unfold AENT. lia.
        + exists (dxG cx), ATABLE. split; [exact Htbl1|]. rewrite RQT. lia. }
    lazymatch goal with
    | HFx : frame_of ?Ev ?rs _ _ |- _ =>
        assert (LAKEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 8 <= x < dxSA cx + 12) ->
          aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x)
        by (intros x Hx Hnx;
            apply (aview_kept_out Ev rs (w_H W1) m1 (ms_mem ms) HFx x Hx);
            intros (rr & Hin & Hr);
            unfold ss_la, la_regions, la_fr, la_ent in Hin; cbn [ss_mem In] in Hin;
            destruct Hin as [<- | [<- | []]];
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?BV32, ?BV2 in Hr; lia)
    end.
    lazymatch goal with
    | HGx : mem_grows _ _ |- _ =>
        assert (LAPRES : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x)
          by (intros x Hp; exact (apresent_grows (w_H W1) m1 (ms_mem ms) x HGx Hp))
    end.
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ev ?ssF ?msF =>
        pose proof (st_ok_pi_region_nth Ev ssF msF 1 _ HS eq_refl) as RGent
    end.
    cbn [ms_mem restrict] in RGent.
    assert (LAVM0 : val_mem SEGS (arm W1 (ms_mem ms)) (dxSA cx + 8) 4 0).
    { change 4%nat with (N.to_nat 4).
      eapply (field_of_region _ _ 32%nat (dxSA cx) _ _ _ _ _ 8 4 (SLit 0) 0);
        [ exact RGent
        | rewrite E32; apply unsigned_lit_small; lia
        | left; reflexivity
        | reflexivity
        | cbn; lia
        | cbn; lia ]. }
    pmkst HS.
    prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
    prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18.
    prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
    prreg HS (27%bv : bv 5) R27. prreg HS (20%bv : bv 5) R20.
    assert (LASK : dskp s1 p = false).
    { destruct HLINK as (_ & _ & Hs & _). destruct (dskp s1 p); [|reflexivity].
      cbn [drain_b_c.ds_skip dvirt] in Hs. lia. }
    assert (LALLZ : Z.of_nat LINE_LIMIT = 6000) by (vm_compute; reflexivity).
    apply HN. apply (DLNOF (ms_regs ms) (ms_mem ms) _).
    * unfold spZ. rewrite R2. exact Usp.
    * rewrite R3; first [exact Hr3 | rewrite (EE 3%nat 3%bv eq_refl); exact Hr3].
    * rewrite R4; first [exact Hr4 | rewrite (EE 4%nat 4%bv eq_refl); exact Hr4].
    * rewrite R21; first [exact Hr21 | rewrite (EE 21%nat 21%bv eq_refl); exact Hr21].
    * rewrite R20; first [exact Hr20 | rewrite (EE 20%nat 20%bv eq_refl); exact Hr20].
    * rewrite R22; first [exact Hr22 | rewrite (EE 22%nat 22%bv eq_refl); exact Hr22].
    * rewrite R27; first [exact Hr27 | rewrite (EE 27%nat 27%bv eq_refl); exact Hr27].
    * rewrite R8; first [exact Hr8 | rewrite (EE 8%nat 8%bv eq_refl); exact Hr8].
    * rewrite R9; first [exact Hr9 | rewrite (EE 9%nat 9%bv eq_refl); exact Hr9].
    * rewrite R18; first [exact Hr18 | rewrite (EE 18%nat 18%bv eq_refl); exact Hr18].
    * rewrite R23, E34. reflexivity.
    * exact LAVM0.
    * exact LAKEEP.
    * exact LAPRES.
    * exact HJ.
    * (* LINE_LIMIT is a unary nat literal: go through Z, never through nat lia *)
      rewrite LASK. cbn [orb]. apply (proj2 (Nat.ltb_lt LINE_LIMIT (q - p))).
      apply (proj2 (Nat2Z.inj_lt LINE_LIMIT (q - p))).
      rewrite LALLZ, Nat2Z.inj_sub by (clear - Hpq; lia).
      clear - Hc. lia.
- (* s->skip = 1: the skip arm *)
  pose proof (HSOK 1 Hsk1 ltac:(lia)) as HS.
  paj_run_to_tok_xR RUNTOR HS HJ SHOK la_Bspan A_dr_next.
  { unfold ss_la, la_regions, la_fr, la_ent. cbn [ss_mem].
    apply awr_ok_x_cons.
    - cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. intros a Ha. exfalso. clear - Ha. lia.
    - apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]. rewrite BV32. intros a Ha.
      left. split; [|lia]. right. left. split.
      + unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
        cbn [fst snd]. unfold AENT. lia.
      + exists (dxG cx), ATABLE. split; [exact Htbl1|]. rewrite RQT. lia. }
  (* the store left s->skip = 0; every other byte and all presence are kept *)
  lazymatch goal with
  | HFx : frame_of ?Ev ?rs _ _ |- _ =>
      assert (LAKEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (dxSA cx + 8 <= x < dxSA cx + 12) ->
        aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x)
      by (intros x Hx Hnx;
          apply (aview_kept_out Ev rs (w_H W1) m1 (ms_mem ms) HFx x Hx);
          intros (rr & Hin & Hr);
          unfold ss_la, la_regions, la_fr, la_ent in Hin; cbn [ss_mem In] in Hin;
          destruct Hin as [<- | [<- | []]];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?BV32, ?BV2 in Hr; lia)
  end.
  lazymatch goal with
  | HGx : mem_grows _ _ |- _ =>
      assert (LAPRES : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x)
        by (intros x Hp; exact (apresent_grows (w_H W1) m1 (ms_mem ms) x HGx Hp))
  end.
  (* s->skip's four bytes, read off the final state's entry region *)
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ssF ?msF =>
      pose proof (st_ok_pi_region_nth Ev ssF msF 1 _ HS eq_refl) as RGent
  end.
  cbn [ms_mem restrict] in RGent.
  assert (LAVM0 : val_mem SEGS (arm W1 (ms_mem ms)) (dxSA cx + 8) 4 0).
  { change 4%nat with (N.to_nat 4).
    eapply (field_of_region _ _ 32%nat (dxSA cx) _ _ _ _ _ 8 4 (SLit 0) 0);
      [ exact RGent
      | rewrite E32; apply unsigned_lit_small; lia
      | left; reflexivity
      | reflexivity
      | cbn; lia
      | cbn; lia ]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18.
  prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
  prreg HS (27%bv : bv 5) R27. prreg HS (20%bv : bv 5) R20.
  assert (LASK : dskp s1 p = true).
  { destruct HLINK as (_ & _ & Hs & _). destruct (dskp s1 p); [reflexivity|].
    cbn [drain_b_c.ds_skip dvirt] in Hs. lia. }
  apply HN. apply (DLNOF (ms_regs ms) (ms_mem ms) _).
  + unfold spZ. rewrite R2. exact Usp.
  + rewrite R3; first [exact Hr3 | rewrite (EE 3%nat 3%bv eq_refl); exact Hr3].
  + rewrite R4; first [exact Hr4 | rewrite (EE 4%nat 4%bv eq_refl); exact Hr4].
  + rewrite R21; first [exact Hr21 | rewrite (EE 21%nat 21%bv eq_refl); exact Hr21].
  + rewrite R20; first [exact Hr20 | rewrite (EE 20%nat 20%bv eq_refl); exact Hr20].
  + rewrite R22; first [exact Hr22 | rewrite (EE 22%nat 22%bv eq_refl); exact Hr22].
  + rewrite R27; first [exact Hr27 | rewrite (EE 27%nat 27%bv eq_refl); exact Hr27].
  + rewrite R8; first [exact Hr8 | rewrite (EE 8%nat 8%bv eq_refl); exact Hr8].
  + rewrite R9; first [exact Hr9 | rewrite (EE 9%nat 9%bv eq_refl); exact Hr9].
  + rewrite R18; first [exact Hr18 | rewrite (EE 18%nat 18%bv eq_refl); exact Hr18].
  + rewrite R23, E34. reflexivity.
  + exact LAVM0.
  + exact LAKEEP.
  + exact LAPRES.
  + exact HJ.
  + rewrite LASK. reflexivity.
Qed.
End wR.
(* the strict texts are the R twins above at R := wle: each R premise at wle is the strict hypothesis of the same
   name, and the three laws hold for wle *)
Local Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* What a callee's journal keeps (la_keep_high / la_keep_img / la_keep_blk / la_gx_frames over ajournal_gx_x; the image
   clause of YCbqG.ajournal_x has the program statics' premise ~ Exists (in_zr a) PST) *)
Lemma la_keep_high_x : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G ->
@ajournal_gx_x _ SK SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
eapply (la_keep_high_xR (@wle SEGS)); wle_inst.
Qed.

Lemma la_keep_img_x : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
@ajournal_gx_x _ SK SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> fp_spares FP a -> ~ inG G a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
eapply (la_keep_img_xR (@wle SEGS)); wle_inst.
Qed.

(* The bytes of a block that is live on BOTH sides of the call and is not in the callee's footprint. *)
Lemma la_keep_blk_x : forall G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
@ajournal_gx_x _ SK SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> ~ inG G (p + i) -> 0 <= p + i < 2 ^ 64 ->
aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
eapply (la_keep_blk_xR (@wle SEGS)); wle_inst.
Qed.

(* A callee that owns no new frame leaves the caller's frame list alone. *)
Lemma la_gx_frames_x : forall G XO OUT STK sp0 FP ly S Hp W mem md ly' S' Hp' W' mem' md' k,
@ajournal_gx_x _ SK SEGS B PST ARx G XO OUT STK sp0 FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
frames S' = frames S.
Proof.
eapply (la_gx_frames_xR (@wle SEGS)); wle_inst.
Qed.

(* gs_cut_facts / gs_cut_dnext_signs (W_drain_tr.v, stated over LCORE) over LCORE_x: what a line-loop cut's core gives
   by itself, the same proofs *)
Lemma la_cut_facts_x : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
  LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
    spent tl ->
  nozero (drain_b_c.ds_u s1) /\ 0 <= drain_b_c.ds_cap s1 /\ 0 <= dxmx cx /\ 0 <= no /\ 0 <= oc /\ 0 <= ka /\
  0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1).
Proof.
eapply (la_cut_facts_xR (@wle SEGS)); wle_inst.
Qed.

Lemma la_cut_dnext_signs_x : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl p,
  0 <= dxmx cx -> dbound s1 p -> no = dlno s1 p -> oc = dloc cx s1 p -> (0 <= ka -> 0 <= dlka cx s1 p) ->
  LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
    spent tl ->
  0 <= oc /\
  0 <= drain_b_c.ds_cap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1).
Proof.
eapply (la_cut_dnext_signs_xR (@wle SEGS)); wle_inst.
Qed.

(* ---- THE SEGMENT over ARx: DLL_x 0x8399c -> DLN_x (S q) 0x839d4, or through send_line DLS_x 0x839f4 -> LINEB ---- *)
Theorem dr_linea_x : dr_linea_stmt_x B PST ARx MT RP MMAX RG.
Proof.
eapply (dr_linea_xR (@wle SEGS)); wle_inst.
Qed.

End cx.
End b.
End a.
