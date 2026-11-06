(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the shared machine-state helpers of segment GS of the ASan+UBSan walk
   (image B, fuzz_reply.asan-ubsan) of fuzz_reply's drain -- gesture_seen's held-array search and update
   (relay.c:89-121, inlined) -- that the three stage walks of lib/B/W_drain_gs.v (gs_scan_stmt, gs_add_stmt,
   gs_free_stmt) cite: the relay entry kept across a step, opening and closing the walk's journal at an
   allocator site, the meters over an append, a kept footprint below alloc_ceiling, an allocator rule's mo_ok
   from dbud, and the signs of the requests the cut predicates still owe.

   PORTED from image A on a working branch 0c06ccc287f, every lemma name kept:
     lib/A/W_drain_gs.v:668-791 (last changed in 1ef2c00b5d5): gs_aentry_okx_kept, gs_gx_open, gs_gx_close,
       gs_tr_cost_app, gs_tr_alloc_app, gs_tr_max_nonneg, gs_tr_max_app, gs_kept_lo, gs_akept_of, gs_mo_ok_of;
     lib/A/W_drain_tr.v:113-547 (last changed in 333e49d6f5f): tr_sizes_ok, gs_tr_cost_nonneg,
       gs_tr_alloc_nonneg, gs_dlfut_sizes, gs_dsfut_sizes, gs_dnext_signs_at, gs_cut_facts, gs_cut_dnext_signs,
       gs_dgs_dnext_signs, and what they need (sz_*, dr_run_sizes, gs_dlater_sizes, tr_drl_split).
   No lemma names an image address or an image-A number.  Each is stated over image B's own interface:
   lib/B/W_drain_cx.v's aentry_okx (:373), dlater / dbud / dlfut / dsfut (:475-507), DMEM (:566), DLINK (:586),
   DHIST (:603), dvirt (:619), RSTART (:644) and LCORE (:650), and lib/B's W_rep (akept, aentry_fp,
   aentry_blks, asrc_at, aout_at), W_journal (ajournal_gx), W_frame (writable_kept) and W_contract (tr_cost,
   tr_alloc, tr_max); those texts are image A's, conjunct for conjunct, so A's proofs carry over unchanged.
   W_drain_tr.v's restatements of W_drain_gs.v's model (tr_lrun_app, tr_lrun_one, tr_drlp_line, tr_dline_len,
   ...) and the two lemmas of A's W_drain_rest_model.v it uses (rmx_scan_nz0, rmx_scan_pre) are not restated:
   their B twins are lib/B/W_drain_gs_model.v's gsx_lrun_app, gs_dlrun, gs_dlno, gs_drl, gsx_scan_nz_app and
   gsx_scan_pre.
   NOT PORTED from W_drain_tr.v: dr_di_signs, gs_dgrow_signs and dr_di_later_meters (the TOP stage's DI cut,
   whose B text has one conjunct more than A's), gs_dnext_signs and gs_tr_sizes_app; neither A's GS pieces nor
   the lemmas here cite them.  A's shared scratch files W_gsbytes_scratch.v and W_gsmodel_scratch.v: A's GS
   pieces Require neither, and every W_gsmodel_scratch.v lemma they cite is already in W_drain_gs_model.v.

   The Section c header is lib/B/W_drain_cx.v's, verbatim (as lib/B/W_drain_gs.v carries it).  Every lemma is
   `Proof using` exactly the section variables its statement names, so a piece applies it to those and to
   nothing else: gs_aentry_okx_kept / gs_gx_open / gs_gx_close to B; gs_tr_cost_app to MT; gs_mo_ok_of to
   MT MMAX MTL; gs_tr_cost_nonneg to MT MTL; gs_cut_facts / gs_cut_dnext_signs / gs_dgs_dnext_signs to
   B MT MMAX RG; the others to no section variable. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_drain_gs_aux.v; 144 of its 528 lines of code are new or changed and 295 lines of the source are left out. *)
(* Image-B (fuzz_reply.asan-ubsan) copy of lib/A/W_drain_tr.v (a working branch e6b5f95b285), over lib/B's
   interface; only the imports and the Section header (lib/B/W_drain_lineb.v's) changed. *)
(* The sign of the requests still owed by fuzz_reply's drain (image A's original: ASan walk, fuzz_reply.asan 0x830dc .. 0x83de4; image B's: fuzz_reply.asan-ubsan 0x83278 .. 0x841fc).
   dbud carries the cost, the live bytes and the largest request of the trace tl still to come, not that its
   requested sizes are nonnegative; every allocator site of the walk (GS add / free, TOP, DROP) needs that sign
   to split the budget (tr_cost / tr_alloc of a suffix is nonnegative).  tr_sizes_ok says it; gs_dlater_sizes
   proves it of every trace dlater names, by induction on drain_run's fuel (grow_tr, pushes_run with
   ListTr.list_push_tra, ListTr.list_drop_tra, lines_run with send_line's sl_run and seen_tr), carrying
   0 <= ds_cap, ds_ecap, ds_ocap across the rounds.  It needs sign premises on the state: a state with a
   negative s->cap grows it by RRealloc cap (2 cap), a negative size.  The Section header is W_drain_cx.v's. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx W_drain_rest_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

(* the pure lemmas below need no Section hypothesis; clear them so that lia's proof term mentions none *)
Ltac clr0 := repeat match goal with H : _ |- _ => clear H end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

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

Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- Every request of the trace asks a nonnegative size (a free asks none). ---- *)
Definition tr_sizes_ok (t : dtrace) : Prop :=
Forall (fun ev => match ev with
  | RelayRunT.RMalloc n => 0 <= n
  | RelayRunT.RRealloc _ n _ => 0 <= n
  | RelayRunT.RFree _ _ => True
  end) t.

Lemma gs_tr_cost_nonneg : forall t, tr_sizes_ok t -> 0 <= tr_cost MT t.
Proof using MTL. clear - MTL.
intros t H. unfold tr_sizes_ok in H. unfold tr_cost.
pose proof (mo_free_nonneg MT MTL) as HF.
induction H as [|ev t Hev Ht IH]; cbn [fold_right]; [lia|].
destruct ev as [n|n a|k n a]; cbv beta iota in Hev |- *.
- pose proof (mo_malloc_nonneg MT MTL n Hev). lia.
- lia.
- pose proof (mo_malloc_nonneg MT MTL n Hev). lia.
Qed.

Lemma gs_tr_alloc_nonneg : forall t, tr_sizes_ok t -> 0 <= tr_alloc t.
Proof using. clr0.
intros t H. unfold tr_sizes_ok in H. unfold tr_alloc.
induction H as [|ev t Hev Ht IH]; cbn [fold_right]; [lia|].
destruct ev as [n|n a|k n a]; cbv beta iota in Hev |- *; lia.
Qed.

Lemma gs_tr_sizes_app : forall t1 t2, tr_sizes_ok (t1 ++ t2) -> tr_sizes_ok t1 /\ tr_sizes_ok t2.
Proof using.
intros t1 t2 H. unfold tr_sizes_ok in *. apply Forall_app in H. exact H.
Qed.

(* ---- The pieces of a round. ---- *)
Lemma sz_nil : tr_sizes_ok [].
Proof using. apply Forall_nil. Qed.

Lemma sz_app2 : forall t1 t2, tr_sizes_ok t1 -> tr_sizes_ok t2 -> tr_sizes_ok (t1 ++ t2).
Proof using. intros t1 t2 H1 H2. unfold tr_sizes_ok in *. apply Forall_app. split; assumption. Qed.

Lemma sz_malloc : forall n (t : dtrace), 0 <= n -> tr_sizes_ok t -> tr_sizes_ok (RelayRunT.RMalloc n :: t).
Proof using. intros n t Hn Ht. apply Forall_cons; [exact Hn | exact Ht]. Qed.

Lemma sz_realloc : forall k n (a : dadrF) (t : dtrace), 0 <= n -> tr_sizes_ok t ->
  tr_sizes_ok (RelayRunT.RRealloc k n a :: t).
Proof using. intros k n a t Hn Ht. apply Forall_cons; [exact Hn | exact Ht]. Qed.

Lemma sz_free : forall n (a : dadrF) (t : dtrace), tr_sizes_ok t -> tr_sizes_ok (RelayRunT.RFree n a :: t).
Proof using. intros n a t Ht. apply Forall_cons; [exact I | exact Ht]. Qed.

Lemma sz_drop_if : forall (bb : bool) (x : dadrF) n, tr_sizes_ok (if bb then ListTr.list_drop_tra x n else []).
Proof using. intros bb x n. destruct bb; [unfold ListTr.list_drop_tra; apply sz_free|]; exact sz_nil. Qed.

(* the buffer's growth: 8192 or 2 cap *)
Lemma sz_grow : forall cap used j b, 0 <= cap ->
  tr_sizes_ok (fst (drain_b_c.grow_tr cap used j b)) /\ 0 <= fst (snd (drain_b_c.grow_tr cap used j b)).
Proof using. clr0.
intros cap used j b Hc. unfold drain_b_c.grow_tr.
destruct (cap - used <? 4096); cbn [fst snd]; [|split; [exact sz_nil | exact Hc]].
destruct (cap =? 0); cbn beta iota zeta; split.
- apply sz_malloc; [lia | exact sz_nil].
- lia.
- apply sz_realloc; [lia | exact sz_nil].
- lia.
Qed.

(* send_line's rounds: a growth asks (no + n) * 2 > 2 cap *)
Lemma sz_sl_run : forall f mx no cap rem j o, 0 <= cap ->
  tr_sizes_ok (fst (send_line_b_c.sl_run f mx no cap rem j o)) /\
  0 <= fst (snd (send_line_b_c.sl_run f mx no cap rem j o)).
Proof using. clr0.
induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run].
- cbn [fst snd]. split; [exact sz_nil | exact Hc].
- destruct (rem <=? 0); [cbn [fst snd]; split; [exact sz_nil | exact Hc]|].
  match goal with |- context [Z.ltb cap ?x] => destruct (Z.ltb_spec cap x) as [Hlt|Hge] end.
  + match goal with |- context [send_line_b_c.sl_run f ?a1 ?a2 ?a3 ?a4 ?a5 ?a6] =>
      assert (Hc' : 0 <= a3) by lia; destruct (IH a1 a2 a3 a4 a5 a6 Hc') as [I1 I2] end.
    cbn [fst snd]. split; [|exact I2].
    destruct (cap =? 0); cbn beta iota; [apply sz_malloc | apply sz_realloc]; (exact Hc' || exact I1).
  + apply IH. exact Hc.
Qed.

Lemma sz_send_line : forall live mx no cap len j o, 0 <= cap ->
  tr_sizes_ok (send_line_b_c.send_line_tr live mx no cap len j o) /\
  0 <= send_line_b_c.send_line_cap live mx no cap len.
Proof using.
intros live mx no cap len j o Hc. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
destruct live; [|split; [exact sz_nil | exact Hc]].
split; [exact (proj1 (sz_sl_run _ _ _ _ _ _ _ Hc)) | exact (proj2 (sz_sl_run _ _ _ _ _ _ _ Hc))].
Qed.

(* gesture_seen: (|H| + 1) * 8 and |x| + 1, or a free *)
Lemma sz_seen : forall H ka l j ha ks, tr_sizes_ok (fst (fst (drain_b_c.seen_tr H ka l j ha ks))).
Proof using. clr0.
intros H ka l j ha ks. unfold drain_b_c.seen_tr.
destruct (gesture l) as [[kd x]|]; [|exact sz_nil].
destruct kd; cbn beta iota; destruct (index_of x H); cbn [fst snd]; try exact sz_nil.
- destruct (ka =? 0); cbn beta iota; [apply sz_malloc | apply sz_realloc]; [lia | | lia |];
    (apply sz_malloc; [lia | exact sz_nil]).
- apply sz_free. exact sz_nil.
Qed.

Lemma sz_lines_run : forall ls live mx no cap H ka j o ha ks, 0 <= cap ->
  tr_sizes_ok (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) /\
  0 <= fst (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))).
Proof using.
induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks Hc; cbn [drain_b_c.lines_run].
- cbn [fst snd]. split; [exact sz_nil | exact Hc].
- destruct (sz_send_line live mx no cap (Z.of_nat (length l) + 1) j o Hc) as [S1 S2].
  match goal with |- context [drain_b_c.lines_run live mx ?a1 ?a2 ?a3 ?a4 r ?a5 ?a6 ?a7 ?a8] =>
    destruct (IH live mx a1 a2 a3 a4 a5 a6 a7 a8 S2) as [I1 I2] end.
  cbn [fst snd]. split; [|exact I2].
  apply sz_app2; [exact S1|]. apply sz_app2; [apply sz_seen | exact I1].
Qed.

(* reference_feed's pushes: the grown array (128 or 32 cap) and the text (|l| + 1) *)
Lemma sz_pushes_run : forall ls n cap j v rs, 0 <= cap ->
  tr_sizes_ok (fst (fst (drain_b_c.pushes_run n cap ls j v rs))) /\
  0 <= snd (fst (drain_b_c.pushes_run n cap ls j v rs)).
Proof using. clr0.
induction ls as [|l r IH]; intros n cap j v rs Hc; cbn [drain_b_c.pushes_run].
- cbn [fst snd]. split; [exact sz_nil | exact Hc].
- assert (Hpc : 0 <= drain_b_c.push_cap n cap).
  { unfold drain_b_c.push_cap. destruct (n =? cap); [destruct (cap =? 0)|]; lia. }
  match goal with |- context [drain_b_c.pushes_run ?a1 ?a2 r ?a3 ?a4 ?a5] =>
    destruct (IH a1 a2 a3 a4 a5 Hpc) as [I1 I2] end.
  cbn [fst snd]. split; [|exact I2]. apply sz_app2; [|exact I1].
  unfold ListTr.list_push_tra. apply sz_app2; [|apply sz_malloc; [lia | exact sz_nil]].
  destruct (n =? cap); [|exact sz_nil].
  destruct (cap =? 0); cbn beta iota; [apply sz_malloc | apply sz_realloc]; [lia | exact sz_nil | lia | exact sz_nil].
Qed.

(* drain's rounds, with s->cap, the expected list's capacity and g_capout nonnegative *)
Lemma dr_run_sizes : forall f live mx s j a,
  0 <= drain_b_c.ds_cap s -> 0 <= drain_b_c.ds_ecap s -> 0 <= drain_b_c.ds_ocap s ->
  tr_sizes_ok (fst (drain_b_c.drain_run f live mx s j a)).
Proof using.
induction f as [|f IH]; intros live mx s j a Hc He Ho; [exact sz_nil|].
cbn [drain_b_c.drain_run].
destruct (sz_grow (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) Hc)
  as [G1 G2].
destruct (drain_b_c.ds_eintr s).
- cbn [fst]. apply sz_app2; [exact G1|]. apply IH; [exact G2 | exact He | exact Ho].
- destruct (drain_b_c.ds_pend s) as [|r0 rs]; [exact G1|].
  match goal with |- context [Z.leb ?x 0] => destruct (Z.leb x 0) end; [exact G1|].
  match goal with |- context [RelayModel.chunk ?u ?k ?d] =>
    destruct (RelayModel.chunk u k d) as [[u' sk'] rl] end.
  cbn beta iota.
  match goal with |- context [drain_b_c.pushes_run ?n ?c ?ls ?jj ?v ?rs] =>
    destruct (sz_pushes_run ls n c jj v rs He) as [P1 P2] end.
  match goal with |- context [drain_b_c.lines_run ?l1 ?l2 ?l3 ?l4 ?l5 ?l6 ?l7 ?l8 ?l9 ?l10 ?l11] =>
    pose proof (sz_lines_run l7 l1 l2 l3 l4 l5 l6 l8 l9 l10 l11 Ho) as [L1 L2];
    revert L1 L2;
    destruct (drain_b_c.lines_run l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11) as [[tl [[oc' H'] ka']] [[o' ha'] ks']];
    intros L1 L2 end.
  cbn [fst snd] in L1, L2 |- *.
  apply sz_app2; [exact G1|]. apply sz_app2; [exact P1|]. apply sz_app2; [apply sz_drop_if|].
  apply sz_app2; [exact L1|]. apply IH; [exact G2 | exact P2 | exact L2].
Qed.

(* ---- The trace dlater names: every request asks a nonnegative size.  FALSE without the signs of s (a
   negative s->cap grows to 2 s->cap); the cut predicates give them (DLINK / aentry_okx: ds_cap = re_cap in
   {0, 8192, 16384}, ds_ka = ent_ka; aout_at: 0 <= no, 0 <= cap; asrc_at: the expected list).  The proof uses
   the signs of ds_cap, ds_ocap and ds_ecap (dr_run_sizes). ---- *)
Lemma gs_dlater_sizes : forall cx s jb a t, 0 <= dxmx cx ->
  0 <= drain_b_c.ds_cap s -> 0 <= drain_b_c.ds_ocap s -> 0 <= drain_b_c.ds_no s ->
  0 <= drain_b_c.ds_en s -> 0 <= drain_b_c.ds_ecap s -> 0 <= drain_b_c.ds_ka s ->
  dlater cx s jb a t -> tr_sizes_ok t.
Proof using.
intros cx s jb a t _ Hc Ho _ _ He _ HL. unfold dlater in HL.
destruct HL as (fuel & _ & _ & Ht & _). subst t.
apply dr_run_sizes; assumption.
Qed.

(* ---- The line loop's cuts: their owed trace is gesture_seen's (dsfut), then the lines' (dlfut), then
   dlater of the next round state dnext s1.  The six signs pass from s1 to dnext s1. ---- *)
Lemma sz_seen_ka : forall H ka l j ha ks, 0 <= ka -> 0 <= snd (fst (drain_b_c.seen_tr H ka l j ha ks)).
Proof using. clr0.
intros H ka l j ha ks Hk. unfold drain_b_c.seen_tr.
destruct (gesture l) as [[kd x]|]; [|exact Hk].
destruct kd; cbn beta iota; destruct (index_of x H); cbn [fst snd]; lia.
Qed.

Lemma sz_lines_run_ka : forall ls live mx no cap H ka j o ha ks, 0 <= ka ->
  0 <= snd (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))).
Proof using. clr0.
induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks Hk; cbn [drain_b_c.lines_run].
- cbn [fst snd]. exact Hk.
- match goal with |- context [drain_b_c.lines_run live mx ?a1 ?a2 ?a3 ?a4 r ?a5 ?a6 ?a7 ?a8] =>
    exact (IH live mx a1 a2 a3 a4 a5 a6 a7 a8 (sz_seen_ka _ _ _ _ _ _ Hk)) end.
Qed.

Lemma gs_dnext_signs : forall lv mx s,
  0 <= drain_b_c.ds_cap s -> 0 <= drain_b_c.ds_ocap s -> 0 <= drain_b_c.ds_no s ->
  0 <= drain_b_c.ds_en s -> 0 <= drain_b_c.ds_ecap s -> 0 <= drain_b_c.ds_ka s ->
  0 <= drain_b_c.ds_cap (dnext lv mx s) /\ 0 <= drain_b_c.ds_ocap (dnext lv mx s) /\
  0 <= drain_b_c.ds_no (dnext lv mx s) /\ 0 <= drain_b_c.ds_en (dnext lv mx s) /\
  0 <= drain_b_c.ds_ecap (dnext lv mx s) /\ 0 <= drain_b_c.ds_ka (dnext lv mx s).
Proof using. clr0.
intros lv mx s Hc Ho Hn He Hec Hk. unfold dnext, lrun, pcapm.
cbn [drain_b_c.ds_cap drain_b_c.ds_ocap drain_b_c.ds_no drain_b_c.ds_en drain_b_c.ds_ecap drain_b_c.ds_ka].
split; [exact Hc|]. split.
{ match goal with |- context [drain_b_c.lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11] =>
    exact (proj2 (sz_lines_run a7 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 Ho)) end. }
split; [lia|]. split; [lia|]. split.
{ match goal with |- context [drain_b_c.pushes_run ?n ?c ?ls ?jj ?v ?rs] =>
    exact (proj2 (sz_pushes_run ls n c jj v rs Hec)) end. }
match goal with |- context [drain_b_c.lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11] =>
  exact (sz_lines_run_ka a7 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 Hk) end.
Qed.

(* the owed trace of a cut after gesture_seen (DLN, DLL, DLR carry dlfut): g_capout = oc is nonnegative *)
Lemma gs_dlfut_sizes : forall cx s2 ab no oc H ka rl jb o ha ks tl, 0 <= dxmx cx -> 0 <= oc ->
  0 <= drain_b_c.ds_cap s2 -> 0 <= drain_b_c.ds_ocap s2 -> 0 <= drain_b_c.ds_no s2 ->
  0 <= drain_b_c.ds_en s2 -> 0 <= drain_b_c.ds_ecap s2 -> 0 <= drain_b_c.ds_ka s2 ->
  dlfut cx s2 ab no oc H ka rl jb o ha ks tl -> tr_sizes_ok tl.
Proof using.
intros cx s2 ab no oc H ka rl jb o ha ks tl Hmx Hoc Hc Ho Hn He Hec Hk HF.
unfold dlfut in HF. cbv zeta in HF. destruct HF as (tl2 & HL & ->).
apply sz_app2; [exact (proj1 (sz_lines_run rl (dlive cx) (dxmx cx) no oc H ka jb o ha ks Hoc))|].
exact (gs_dlater_sizes cx s2 _ _ tl2 Hmx Hc Ho Hn He Hec Hk HL).
Qed.

(* the owed trace of a cut before gesture_seen (DGS carries dsfut) *)
Lemma gs_dsfut_sizes : forall cx s2 ab H ka l no oc rl jb o ha ks tl, 0 <= dxmx cx -> 0 <= oc ->
  0 <= drain_b_c.ds_cap s2 -> 0 <= drain_b_c.ds_ocap s2 -> 0 <= drain_b_c.ds_no s2 ->
  0 <= drain_b_c.ds_en s2 -> 0 <= drain_b_c.ds_ecap s2 -> 0 <= drain_b_c.ds_ka s2 ->
  dsfut cx s2 ab H ka l no oc rl jb o ha ks tl -> tr_sizes_ok tl.
Proof using.
intros cx s2 ab H ka l no oc rl jb o ha ks tl Hmx Hoc Hc Ho Hn He Hec Hk HF.
unfold dsfut in HF. cbv zeta in HF. destruct HF as (tl2 & HL & ->).
apply sz_app2; [apply sz_seen|].
exact (gs_dlfut_sizes cx s2 ab no oc _ _ rl _ o _ _ tl2 Hmx Hoc Hc Ho Hn He Hec Hk HL).
Qed.

(* ---- The signs of dnext s1 from a line-loop cut's own facts.  A cut at p (DLL / DLN / DLR at p; DGS and the
   GS arms at S q) knows the loop's running values dlno / dloc / dlka at p, not s1's own g_capout / held array
   size; dnext's are those of the lines drlq s1 p still to come from them (drl s1 = drlp s1 p ++ drlq s1 p).
   dnext's ds_en / ds_ecap are the cut's own (DLINK of dvirt), so they are not part of this lemma. ---- *)
Lemma tr_drl_split : forall s1 p, nozero (drain_b_c.ds_u s1) -> dbound s1 p -> drl s1 = drlp s1 p ++ drlq s1 p.
Proof using. clr0.
intros s1 p HU HB.
assert (E : drl s1 = snd (scan (drain_b_c.ds_skip s1) [] (dW s1))).
{ unfold drl, dchunk, RelayModel.chunk, dW. rewrite (rmx_scan_nz0 _ _ _ HU).
  destruct (scan (drain_b_c.ds_skip s1) (drain_b_c.ds_u s1) (ddata s1)) as [[sk r] ls].
  destruct (Nat.ltb LINE_LIMIT (length r)); reflexivity. }
rewrite E, <- (firstn_skipn p (dW s1)). exact (proj2 (rmx_scan_pre s1 p (skipn p (dW s1)) HB)).
Qed.

(* ported from W_drain_gs.v gsx_lrun_app (= lib/Prog/drain_b.v lrun_app) *)
Lemma tr_lrun_app : forall lv mx0 l1 l2 no0 cp0 H0 ka0,
  lrun lv mx0 no0 cp0 H0 ka0 (l1 ++ l2) =
  lrun lv mx0 (no0 + Z.of_nat (length (with_nul l1))) (fst (fst (lrun lv mx0 no0 cp0 H0 ka0 l1)))
    (snd (fst (lrun lv mx0 no0 cp0 H0 ka0 l1))) (snd (lrun lv mx0 no0 cp0 H0 ka0 l1)) l2.
Proof using. clr0.
  intros lv mx0 l1. induction l1 as [|l r IH]; intros l2 no0 cp0 H0 ka0.
  - rewrite app_nil_l. change (with_nul []) with (@nil Z). cbn [length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - assert (C : forall nb cb Hb kb ls, lrun lv mx0 nb cb Hb kb (l :: ls) =
                 lrun lv mx0 (nb + (Z.of_nat (length l) + 1))
                   (send_line_b_c.send_line_cap lv mx0 nb cb (Z.of_nat (length l) + 1))
                   (seen_arr Hb l) (seen_ka Hb kb l) ls).
    { intros nb cb Hb kb ls. unfold lrun at 1. cbn [drain_b_c.lines_run fst snd]. rewrite lines_run_m, seen_tr_m.
      reflexivity. }
    rewrite <- app_comm_cons, !C, IH.
    replace (no0 + (Z.of_nat (length l) + 1) + Z.of_nat (length (with_nul r)))
      with (no0 + Z.of_nat (length (with_nul (l :: r))))
      by (change (with_nul (l :: r)) with ((l ++ [0]) ++ with_nul r); rewrite !length_app; cbn [length]; lia).
    reflexivity.
Qed.

Lemma gs_dnext_signs_at : forall cx s1 p, nozero (drain_b_c.ds_u s1) -> dbound s1 p ->
  0 <= drain_b_c.ds_cap s1 -> 0 <= dlno s1 p -> 0 <= dloc cx s1 p -> 0 <= dlka cx s1 p ->
  0 <= drain_b_c.ds_cap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1).
Proof using. clr0.
intros cx s1 p HU HB Hc Hno Hoc Hka.
pose proof (tr_drl_split s1 p HU HB) as ED.
assert (E : lrun (dlive cx) (dxmx cx) (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1) (drain_b_c.ds_H s1)
              (drain_b_c.ds_ka s1) (drl s1) =
            lrun (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p) (drlq s1 p)).
{ rewrite ED, tr_lrun_app. reflexivity. }
unfold dnext. cbn [drain_b_c.ds_cap drain_b_c.ds_ocap drain_b_c.ds_no drain_b_c.ds_ka]. rewrite E.
split; [exact Hc|]. split.
{ unfold lrun. match goal with |- context [drain_b_c.lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11] =>
    exact (proj2 (sz_lines_run a7 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 Hoc)) end. }
split.
{ unfold dlno in Hno. rewrite ED. unfold with_nul in *. rewrite map_app, concat_app, length_app. lia. }
unfold lrun. match goal with |- context [drain_b_c.lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11] =>
  exact (sz_lines_run_ka a7 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 Hka) end.
Qed.

(* ---- What a line-loop cut's LCORE gives by itself.  It says nothing of s1's own g_nout / g_capout / held
   array size (the loop carries its running values no / oc / ka instead, dvirt), so the signs of dnext s1's
   ds_ocap / ds_no / ds_ka need the cut's anchor: no / oc / ka are the loop's values dlno / dloc / dlka at
   some p (gs_cut_dnext_signs; DLL / DLN / DLR at p), or at S q for DGS (gs_dgs_dnext_signs). ---- *)
Lemma gs_cut_facts : forall cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
  LCORE B MT MMAX RG cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
  nozero (drain_b_c.ds_u s1) /\ 0 <= drain_b_c.ds_cap s1 /\ 0 <= dxmx cx /\ 0 <= no /\ 0 <= oc /\ 0 <= ka /\
  0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1).
Proof using. clr0.
intros cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl HL.
unfold LCORE in HL. cbv zeta in HL. destruct HL as (HM & HK & _ & HH & HR & _).
assert (Pno : drain_b_c.ds_no (dvirt cx s1 sk H ka no oc) = no) by reflexivity.
assert (Poc : drain_b_c.ds_ocap (dvirt cx s1 sk H ka no oc) = oc) by reflexivity.
assert (Pka : drain_b_c.ds_ka (dvirt cx s1 sk H ka no oc) = ka) by reflexivity.
assert (Pen : drain_b_c.ds_en (dvirt cx s1 sk H ka no oc) = drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1))
  by reflexivity.
assert (Pec : drain_b_c.ds_ecap (dvirt cx s1 sk H ka no oc) = drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1))
  by reflexivity.
unfold DMEM in HM. destruct HM as (_ & _ & _ & _ & _ & _ & _ & HE & HS & _ & _ & HO & _).
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

(* the line loop's values at p give dnext's (DLL / DLN / DLR: no, oc, ka are dlno, dloc, dlka at p) *)
Lemma gs_cut_dnext_signs : forall cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl p,
  0 <= dxmx cx -> dbound s1 p -> no = dlno s1 p -> oc = dloc cx s1 p -> (0 <= ka -> 0 <= dlka cx s1 p) ->
  LCORE B MT MMAX RG cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
  0 <= oc /\
  0 <= drain_b_c.ds_cap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1).
Proof using. clr0.
intros cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl p _ HB Eno Eoc Hka HL.
apply gs_cut_facts in HL. destruct HL as (HU & Hc & _ & Hno & Hoc & Hk & Hen & Hec).
subst no oc.
destruct (gs_dnext_signs_at cx s1 p HU HB Hc Hno Hoc (Hka Hk)) as (D1 & D2 & D3 & D4).
repeat split; assumption.
Qed.

(* ---- DGS's anchor: the line [p, q) is sent (no, oc after it), the held keys not yet updated; the loop's
   values at S q are those (ported from W_drain_gs.v gsx_drl_line / gs_dlno / gs_dlrun). ---- *)
Lemma tr_firstn_split : forall P Q (l : list Z), (P <= Q)%nat -> firstn Q l = firstn P l ++ firstn (Q - P) (skipn P l).
Proof using. clr0.
  induction P as [|P IH]; intros Q l HPQ.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct Q as [|Q]; [lia|]. destruct l as [|a l].
    + rewrite skipn_nil, !firstn_nil. reflexivity.
    + change (a :: firstn Q l = a :: firstn P l ++ firstn (Q - P) (skipn P l)).
      rewrite (IH Q l) by lia. reflexivity.
Qed.

Lemma tr_nz_firstn : forall (l : list Z) k, (forall i, (i < k)%nat -> nth_error l i <> Some 0) -> nozero (firstn k l).
Proof using. clr0.
  unfold nozero. induction l as [|a l IH]; intros k H.
  - rewrite firstn_nil. constructor.
  - destruct k as [|k]; [change (Forall (fun b => b <> 0) (@nil Z)); constructor|].
    change (Forall (fun b => b <> 0) (a :: firstn k l)). constructor.
    + intro E. apply (H 0%nat); [lia|]. rewrite E. reflexivity.
    + apply IH. intros i Hi. exact (H (S i) ltac:(lia)).
Qed.

Lemma tr_dline_nz : forall s1 p q,
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> nozero (dline s1 p q).
Proof using. clr0.
  intros s1 p q H. unfold dline. apply tr_nz_firstn. intros i Hi. rewrite rmx_nth_skipn. apply H. lia.
Qed.

Lemma tr_dline_len : forall s1 p q, (p <= q < length (dW s1))%nat -> length (dline s1 p q) = (q - p)%nat.
Proof using. clr0. intros s1 p q H. unfold dline. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. Qed.

Lemma tr_dW_pre_line : forall s1 p q, (p <= q)%nat -> nth_error (dW s1) q = Some 0 ->
  firstn (S q) (dW s1) = firstn p (dW s1) ++ dline s1 p q ++ [0].
Proof using. clr0.
  intros s1 p q HPQ HQ. rewrite (rmx_firstn_nth_app _ _ _ HQ), (tr_firstn_split p q _ HPQ), <- app_assoc.
  reflexivity.
Qed.

Lemma tr_drlp_line : forall s1 p q, dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> dskp s1 p = false -> (q - p <= LINE_LIMIT)%nat ->
  drlp s1 (S q) = drlp s1 p ++ [dline s1 p q].
Proof using. clr0.
intros s1 p q HB HPQ HQ HNZ HK HL.
pose proof (tr_dline_nz s1 p q HNZ) as Hz.
unfold drlp at 1. rewrite (tr_dW_pre_line s1 p q (proj1 HPQ) HQ), (proj2 (rmx_scan_pre s1 p _ HB)), HK.
rewrite (rmx_scan_nz0 _ false [0] Hz), rmx_scan_zero_snd, (tr_dline_len s1 p q HPQ).
rewrite (proj2 (Nat.ltb_ge LINE_LIMIT (q - p)) HL). reflexivity.
Qed.

Lemma tr_lrun_one : forall lv mx0 no0 cp0 H0 ka0 l,
  lrun lv mx0 no0 cp0 H0 ka0 [l] =
  (send_line_b_c.send_line_cap lv mx0 no0 cp0 (Z.of_nat (length l) + 1), seen_arr H0 l, seen_ka H0 ka0 l).
Proof using.
  intros lv mx0 no0 cp0 H0 ka0 l. unfold lrun. cbn [drain_b_c.lines_run fst snd]. rewrite seen_tr_m. reflexivity.
Qed.

(* DGS (and a GS arm before the held keys change): no / oc after the sent line, ka the array size before it *)
Lemma gs_dgs_dnext_signs : forall cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl p q,
  dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> dskp s1 p = false -> (q - p <= LINE_LIMIT)%nat ->
  no = dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1 ->
  oc = send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
         (Z.of_nat (length (dline s1 p q)) + 1) ->
  (0 <= ka -> 0 <= dlka cx s1 p) ->
  LCORE B MT MMAX RG cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
  0 <= oc /\
  0 <= drain_b_c.ds_cap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1).
Proof using. clr0.
intros cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl p q
  HB HPQ HQ HNZ HK HL Eno Eoc Hka HC.
pose proof (tr_drlp_line s1 p q HB HPQ HQ HNZ HK HL) as E.
assert (HB' : dbound s1 (S q)).
{ split; [lia|]. right. replace (S q - 1)%nat with q by lia. exact HQ. }
assert (ER : dlrun cx s1 (S q) =
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p) (Z.of_nat (length (dline s1 p q)) + 1),
   seen_arr (dlH cx s1 p) (dline s1 p q), seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))).
{ unfold dlrun at 1. rewrite E, tr_lrun_app, tr_lrun_one. reflexivity. }
assert (EN : dlno s1 (S q) = dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1).
{ unfold dlno. rewrite E. unfold with_nul. rewrite map_app, concat_app. cbn [map concat].
  rewrite app_nil_r, !length_app. cbn [length]. lia. }
pose proof (gs_cut_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & _ & Hmx & _).
refine (gs_cut_dnext_signs cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl (S q)
  Hmx HB' _ _ _ HC).
- rewrite EN. exact Eno.
- unfold dloc. rewrite ER. exact Eoc.
- intro Hk. unfold dlka. rewrite ER. cbn [snd]. unfold seen_ka. apply sz_seen_ka. exact (Hka Hk).
Qed.

(* ---- The outer loop's head DI: the six signs of the round state s1 (DI's DLINK is about s1 itself: ds_cap =
   re_cap, ds_ka = ent_ka, ds_en / ds_ecap = the expected list's n / cap; aout_at's g_capout = ds_ocap and
   g_nout = ds_no, or dxno when the output is off, with DHIST's ds_no = dxno + |sent|), kept by the round's
   growth dgrow, and so the sign of what dlater still owes from s1 or dgrow s1. ---- *)
Lemma dr_di_signs : forall cx s1 D W1 c1, DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx s1 D W1 c1 ->
  0 <= dxmx cx /\ 0 <= drain_b_c.ds_cap s1 /\ 0 <= drain_b_c.ds_ocap s1 /\ 0 <= drain_b_c.ds_no s1 /\
  0 <= drain_b_c.ds_en s1 /\ 0 <= drain_b_c.ds_ecap s1 /\ 0 <= drain_b_c.ds_ka s1.
Proof using. clr0.
intros cx s1 D W1 c1 _ HI. unfold DI in HI.
destruct HI as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  _ & _ & HM & _ & _ & _ & HK & _ & HH & _).
unfold DMEM in HM. destruct HM as (_ & _ & _ & _ & _ & _ & _ & HE & HS & _ & _ & HO & _).
unfold aentry_okx in HE. destruct HE as (_ & _ & _ & _ & _ & Hcap & _ & _ & _ & _ & HHP & _).
unfold asrc_at in HS.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HX & _).
unfold alist_at in HX. destruct HX as (_ & _ & _ & _ & (HNC & _) & _).
unfold aout_at in HO.
destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Hmx & HOn & HOc).
unfold DLINK in HK. destruct HK as (Ecap & _ & _ & _ & Eka & _ & _ & _ & _ & Een & Eec & _).
unfold DHIST in HH. destruct HH as (_ & _ & _ & _ & _ & Eno & _).
split; [lia|]. split; [rewrite <- Ecap; lia|].
split; [destruct HOc as [(Hc0 & _)|(Hc0 & _)]; lia|]. split.
{ revert HOn. destruct (dlive cx); intros HOn; cbn beta iota in HOn; lia. }
split; [rewrite <- Een; unfold hl_n; lia|]. split; [rewrite <- Eec; unfold hl_n in HNC; lia|].
rewrite <- Eka. unfold drain_b_c.ent_ka.
destruct HHP as [(H0 & _)|(H0 & _ & _ & H8 & _)];
  [rewrite (proj2 (Z.eqb_eq _ _) H0) | rewrite (proj2 (Z.eqb_neq _ _) H0)]; cbn beta iota; lia.
Qed.

Lemma gs_dgrow_signs : forall s,
  0 <= drain_b_c.ds_cap s -> 0 <= drain_b_c.ds_ocap s -> 0 <= drain_b_c.ds_no s ->
  0 <= drain_b_c.ds_en s -> 0 <= drain_b_c.ds_ecap s -> 0 <= drain_b_c.ds_ka s ->
  0 <= drain_b_c.ds_cap (dgrow s) /\ 0 <= drain_b_c.ds_ocap (dgrow s) /\ 0 <= drain_b_c.ds_no (dgrow s) /\
  0 <= drain_b_c.ds_en (dgrow s) /\ 0 <= drain_b_c.ds_ecap (dgrow s) /\ 0 <= drain_b_c.ds_ka (dgrow s).
Proof using. clr0.
intros s Hc Ho Hn He Hec Hk.
split; [exact (proj2 (sz_grow (drain_b_c.ds_cap s) (ulen s) 0 _ Hc))|].
split; [exact Ho|]. split; [exact Hn|]. split; [exact He|]. split; [exact Hec|]. exact Hk.
Qed.

Lemma dr_di_later_meters : forall cx s1 D W1 c1 jb a tl, DBASE B MT MMAX RG cx -> DI B MT MMAX RG cx s1 D W1 c1 ->
  dlater cx (dgrow s1) jb a tl \/ dlater cx s1 jb a tl -> 0 <= tr_alloc tl /\ 0 <= tr_cost MT tl.
Proof using MTL.
intros cx s1 D W1 c1 jb a tl HB HI HL.
destruct (dr_di_signs cx s1 D W1 c1 HB HI) as (Hmx & Hc & Ho & Hn & He & Hec & Hk).
assert (HT : tr_sizes_ok tl).
{ destruct HL as [HL|HL].
  - destruct (gs_dgrow_signs s1 Hc Ho Hn He Hec Hk) as (Gc & Go & Gn & Ge & Gec & Gk).
    exact (gs_dlater_sizes cx (dgrow s1) jb a tl Hmx Gc Go Gn Ge Gec Gk HL).
  - exact (gs_dlater_sizes cx s1 jb a tl Hmx Hc Ho Hn He Hec Hk HL). }
split; [exact (gs_tr_alloc_nonneg tl HT) | exact (gs_tr_cost_nonneg tl HT)].
Qed.

End c.
End b.
End a.
