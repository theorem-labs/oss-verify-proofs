(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segments FEED and FEEDS of the ASan walk of fuzz_reply's drain -
   reference_feed's byte loop (fuzz_reply.asan 0x8347c .. 0x83550, the call to list_push at 0x834f0) and
   its composition.  The statements are W_drain_cx.v:805 dr_feed_stmt and :851 dr_feeds_stmt; the cut
   predicates are W_drain_cx.v:601 DRB (the loop head, after k of the n bytes) and :619 DE (the loop left).
   The Section header below is W_drain_top.v:44-102 verbatim, so that dr_feed_p / dr_feeds_p carry exactly
   the premises of that file's dr_feed / dr_feeds.

   THE LOOP, as the pinned listing holds it (W_listing.v; address a is entry (a - 0x822ec) / 4, line 41 +
   entry; fr_prog_start = 0x822ec, AF_fr_drain = 0xdf0, AF_fr_list_push = 0x2da4):

     0x8347c  srli a0, s8, 3          the shadow address of the source byte p0 + k
     0x83480  add  a0, a0, s5         s5 = SHADOW_OFF
     0x83484  lb   a0, 0(a0)
     0x83488  bne  a0, zero, 0x83558  -> the partial-granule check, then back to 0x8348c
     0x8348c  lb   a0, 0(s6)          the shadow byte of h->overlong
     0x83490  lbu  a1, 0(s10)         b = *(p0 + k)
     0x83494  bne  a0, zero, 0x83564  -> the 4-byte partial-granule check, then back to 0x83498
     0x83498  lw   a0, 56(s7)         overlong  (s7 = HA = &g_s[j])
     0x8349c  beq  a1, zero, 0x834d0  b = 0: the NUL case
     0x834a0  bne  a0, zero, 0x83544  overlong <> 0: drop the byte
     0x834a4  lbu  a0, 0(s11)         the shadow byte of h->npartial
     0x834a8  bne  a0, zero, 0x83c54  -> __asan_report_load8 (HA + 48)
     0x834ac  ld   a0, 48(s7)         npartial
     0x834b0  lui  a2, 0x1
     0x834b4  addiw a2, a2, 1904      a2 = 6000 = APARTIAL
     0x834b8  bne  a0, a2, 0x83510    npartial <> 6000: the ordinary case
     0x834bc  lb   a0, 0(s6)
     0x834c0  bne  a0, zero, 0x8358c  -> the 4-byte store check, then back to 0x834c4
     0x834c4  addi a0, zero, 1
     0x834c8  sw   a0, 56(s7)         h->overlong = 1
     0x834cc  jal  zero, 0x83544

     the NUL case:
     0x834d0  bne  a0, zero, 0x834f4  overlong <> 0: no push, only the reset
     0x834d4  lbu  a0, 0(s4)          the shadow byte of h->partial
     0x834d8  bne  a0, zero, 0x83c5c  -> __asan_report_load8 (HA + 40)
     0x834dc  lbu  a0, 0(s11)
     0x834e0  bne  a0, zero, 0x83c64  -> __asan_report_load8 (HA + 48)
     0x834e4  ld   a1, 40(s7)         partial
     0x834e8  ld   a2, 48(s7)         npartial
     0x834ec  ld   a0, 72(sp)         &h->expected = HA + 64
     0x834f0  jal  ra, 0x85090        list_push (LPSPEC, BASE + AF_fr_list_push)
     0x834f4  lbu  a0, 0(s11)
     0x834f8  bne  a0, zero, 0x83c6c  -> __asan_report_store8 (HA + 48)
     0x834fc  sd   zero, 48(s7)       h->npartial = 0
     0x83500  lb   a0, 0(s6)
     0x83504  bne  a0, zero, 0x83578  -> the 4-byte store check, then back to 0x83508
     0x83508  sw   zero, 56(s7)       h->overlong = 0
     0x8350c  jal  zero, 0x83544

     the ordinary case:
     0x83510  lbu  a2, 0(s4)
     0x83514  bne  a2, zero, 0x83c74  -> __asan_report_load8 (HA + 40)
     0x83518  lbu  a2, 0(s11)
     0x8351c  bne  a2, zero, 0x83c7c  -> __asan_report_store8 (HA + 48)
     0x83520  ld   a2, 40(s7)         partial
     0x83524  addi a3, a0, 1
     0x83528  sd   a3, 48(s7)         h->npartial = npartial + 1
     0x8352c  add  a0, a2, a0         &partial[npartial]
     0x83530  srli a2, a0, 3
     0x83534  add  a2, a2, s5
     0x83538  lb   a2, 0(a2)
     0x8353c  bne  a2, zero, 0x835a0  -> the 1-byte store check, then back to 0x83540
     0x83540  sb   a1, 0(a0)          partial[npartial] = b

     the loop's tail:
     0x83544  addi s9, s9, -1
     0x83548  addi s8, s8, 1
     0x8354c  addi s10, s10, 1
     0x83550  bne  s9, zero, 0x8347c  -> DRB (S k)
     0x83554  jal  zero, 0x835ac      -> DE (A_dr_fed)

   FEEDS is the composition: by induction on the bytes left, dnum s1 - k.  Each turn of the loop is one
   dr_feed_stmt, and the induction stops because DRB carries `Z.of_nat k < dnum s1`, so a DRB at S k with
   S k = dnum s1 is uninhabited. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
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

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
(* a ROM byte survives a callee's journal (W_journal.v rom_out / ajournal_gx_rom_view): it is not a walk global,
   errno or the sink's overflow head, and if it is an allocator static it is pinned as an AR const cell
   (rom_pinned; W1 45a3cc9bdd0).  The instance discharges it at the pinned placement by vm_compute. *)
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
(* aout_at's three read-only cells are program globals off the allocator's statics, so an allocator or program
   call keeps them (found by GsFree at free #2: they are not in G_DR; send_line's W_send_line_cx.v HGO) *)
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
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 -> aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- helpers shared by the two segments (prefix df_) ---- *)

(* The byte count DRB carries: a cut at k has k of the n bytes behind it and at least one still to feed.
   DRB (W_drain_cx.v:601-646) has 20 existentials, then this is its 30th conjunct (:603).  The projection is
   positional on purpose: a blanket `repeat destruct` unfolds DMEM / ajournal_gx up to conversion and does
   not finish. *)
Lemma df_DRB_bytes : forall cx s1 D k W1 c1,
DRB B MT MMAX RG cx s1 D k W1 c1 -> Z.of_nat k < dnum s1.
Proof.
intros cx s1 D k W1 c1 H.
destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
  ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
  ? & ? & ? & ? & ? & ? & ? & ? & ? & Hk & ?).
exact Hk.
Qed.

(* ---- The reference splitter's one byte (RelayModel.v step / feed_lines). ----
   `feed` and `lines` are folded from the left, and the loop feeds the (k+1)st byte, so every equation
   below is in snoc form: `firstn (S k) d = firstn k d ++ [nth k d]`. *)

Lemma df_firstn_nth_app : forall {A} (l : list A) n x,
nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
intros A l. induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
destruct n as [|n]; cbn [nth_error firstn] in *.
- injection Hn as <-. reflexivity.
- rewrite (IH n x Hn). reflexivity.
Qed.

Lemma df_feed_lines_one : forall st b,
feed_lines st [b] = (fst (step st b), match snd (step st b) with Some l => [l] | None => [] end).
Proof. intros st b. cbn [feed_lines]. destruct (step st b) as [st1 o]. reflexivity. Qed.

Lemma df_feed_one : forall st b, feed st [b] = fst (step st b).
Proof. intros st b. unfold feed. rewrite df_feed_lines_one. reflexivity. Qed.

Lemma df_lines_one : forall st b,
lines st [b] = match snd (step st b) with Some l => [l] | None => [] end.
Proof. intros st b. unfold lines. rewrite df_feed_lines_one. reflexivity. Qed.

Lemma df_feed_snoc : forall st d b, feed st (d ++ [b]) = fst (step (feed st d) b).
Proof. intros st d b. rewrite feed_app, df_feed_one. reflexivity. Qed.

Lemma df_lines_snoc : forall st d b,
lines st (d ++ [b]) =
lines st d ++ match snd (step (feed st d) b) with Some l => [l] | None => [] end.
Proof. intros st d b. rewrite lines_app, df_lines_one. reflexivity. Qed.

(* ---- The splitter's state as the three machine fields hold it. ----
   hs_state h = LS (bzs (hs_W h)) (hs_overlong h =? 1) and hs_W h = firstn (hs_npartial h) (hs_pjunk h)
   (HarnessRep.v:33-35), so h->npartial, h->overlong and the partial buffer decide `step`. *)

Lemma df_bz_of : forall b, 0 <= b < 256 -> bz (Z_to_bv 8 b) = b.
Proof.
intros b Hb. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small. exact Hb.
Qed.

Lemma df_bzs_app : forall l x, bzs (l ++ [x]) = bzs l ++ [bz x].
Proof. intros l x. unfold bzs. rewrite map_app. reflexivity. Qed.

Lemma df_ls_k : forall h, ls_k (hs_state h) = (hs_overlong h =? 1).
Proof. reflexivity. Qed.

Lemma df_ls_w : forall h, ls_w (hs_state h) = bzs (hs_W h).
Proof. reflexivity. Qed.

Lemma df_ls_w_len : forall h, 0 <= hs_npartial h <= APARTIAL ->
Z.of_nat (length (hs_pjunk h)) = APARTIAL ->
length (ls_w (hs_state h)) = Z.to_nat (hs_npartial h).
Proof.
intros h Hnp Hl. rewrite df_ls_w. unfold bzs, hs_W.
rewrite length_map, length_firstn. unfold APARTIAL in *. lia.
Qed.

(* LINE_LIMIT is a nat numeral, i.e. 6000 nested S: never unfold it in front of lia, give lia its value. *)
Lemma df_LL : Z.of_nat LINE_LIMIT = 6000.
Proof. vm_compute. reflexivity. Qed.

(* the four arms of `step`, read off h->overlong, h->npartial and the byte *)
Lemma df_step_skip : forall h b, b <> 0 -> hs_overlong h = 1 -> step (hs_state h) b = (hs_state h, None).
Proof. intros h b Hb Hov. apply step_nz_k; [exact Hb|]. rewrite df_ls_k, Hov. reflexivity. Qed.

Lemma df_step_long : forall h b, b <> 0 -> hs_overlong h = 0 -> hs_npartial h = APARTIAL ->
Z.of_nat (length (hs_pjunk h)) = APARTIAL ->
step (hs_state h) b = (LS (bzs (hs_W h)) true, None).
Proof.
intros h b Hb Hov Hnp Hl.
assert (Hk : ls_k (hs_state h) = false) by (rewrite df_ls_k, Hov; reflexivity).
assert (He : length (ls_w (hs_state h)) = LINE_LIMIT).
{ rewrite (df_ls_w_len h ltac:(unfold APARTIAL in *; lia) Hl).
  pose proof df_LL as LL. unfold APARTIAL in Hnp. lia. }
rewrite (step_nz_full (hs_state h) b Hb Hk He), df_ls_w. reflexivity.
Qed.

Lemma df_step_add : forall h b, b <> 0 -> hs_overlong h = 0 -> hs_npartial h <> APARTIAL ->
0 <= hs_npartial h <= APARTIAL -> Z.of_nat (length (hs_pjunk h)) = APARTIAL ->
step (hs_state h) b = (LS (bzs (hs_W h) ++ [b]) false, None).
Proof.
intros h b Hb Hov Hnp Hle Hl.
assert (Hk : ls_k (hs_state h) = false) by (rewrite df_ls_k, Hov; reflexivity).
assert (He : length (ls_w (hs_state h)) <> LINE_LIMIT).
{ rewrite (df_ls_w_len h Hle Hl). pose proof df_LL as LL. unfold APARTIAL in *. lia. }
rewrite (step_nz_add (hs_state h) b Hb Hk He), df_ls_w. reflexivity.
Qed.

Lemma df_step_push : forall h, hs_overlong h = 0 ->
step (hs_state h) 0 = (LS [] false, Some (bzs (hs_W h))).
Proof. intros h Hov. rewrite step_zero, df_ls_k, df_ls_w, Hov. reflexivity. Qed.

Lemma df_step_reset : forall h, hs_overlong h = 1 -> step (hs_state h) 0 = (LS [] false, None).
Proof. intros h Hov. rewrite step_zero, df_ls_k, Hov. reflexivity. Qed.

(* ---- The state the machine leaves, in each arm, is the state `step` names. ----
   The machine writes h->npartial and h->overlong and (in the ordinary arm) one byte of the partial
   buffer; these say that the record it leaves has the splitter state the model asks for. *)

Lemma df_state_skip : forall h1 h2, hs_npartial h2 = hs_npartial h1 -> hs_overlong h2 = hs_overlong h1 ->
hs_pjunk h2 = hs_pjunk h1 -> hs_state h2 = hs_state h1.
Proof.
intros h1 h2 Hnp Hov Hpj. unfold hs_state, hs_W. rewrite Hnp, Hov, Hpj. reflexivity.
Qed.

Lemma df_state_long : forall h1 h2, hs_npartial h2 = hs_npartial h1 -> hs_overlong h2 = 1 ->
hs_pjunk h2 = hs_pjunk h1 -> hs_state h2 = LS (bzs (hs_W h1)) true.
Proof.
intros h1 h2 Hnp Hov Hpj. unfold hs_state, hs_W. rewrite Hnp, Hov, Hpj. reflexivity.
Qed.

Lemma df_state_reset : forall h2, hs_npartial h2 = 0 -> hs_overlong h2 = 0 ->
hs_state h2 = LS [] false.
Proof.
intros h2 Hnp Hov. unfold hs_state, hs_W. rewrite Hnp, Hov. reflexivity.
Qed.

Lemma df_state_add : forall h1 h2 b,
hs_overlong h2 = 0 -> hs_npartial h2 = hs_npartial h1 + 1 -> 0 <= hs_npartial h1 ->
firstn (Z.to_nat (hs_npartial h1)) (hs_pjunk h2) = firstn (Z.to_nat (hs_npartial h1)) (hs_pjunk h1) ->
nth_error (hs_pjunk h2) (Z.to_nat (hs_npartial h1)) = Some (Z_to_bv 8 b) ->
0 <= b < 256 ->
hs_state h2 = LS (bzs (hs_W h1) ++ [b]) false.
Proof.
intros h1 h2 b Hov Hnp H0 Hpre Hat Hb.
unfold hs_state, hs_W. rewrite Hov, Hnp.
replace (Z.to_nat (hs_npartial h1 + 1)) with (S (Z.to_nat (hs_npartial h1))) by lia.
rewrite (df_firstn_nth_app (hs_pjunk h2) (Z.to_nat (hs_npartial h1)) (Z_to_bv 8 b) Hat), Hpre.
rewrite df_bzs_app, (df_bz_of b Hb). reflexivity.
Qed.

(* ---- The symbolic state at DRB (0x8347c). ----
   Registers the cut pins: s5 = 21 = SHADOW_OFF, s7 = 23 = HA, s3 = 19 = n, s9 = 25 = n - k,
   s8 = 24 and s10 = 26 = p0 + k, and the three shadow-address registers s4 = 20, s11 = 27, s6 = 22,
   which must carry the `shadow_addr` SHAPE (not just its value) so that the engine recognises the
   shadow loads at 0x8348c / 0x834a4 / 0x834d4 as covered by the SH entry on atom 23.
   Extra atoms: 32 = h->partial, 33 = h->npartial, 34 = h->overlong, 35 = the byte at p0 + k. *)
Definition df_shv (m : nat) (c : Z) : sv :=
SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 21 0).

Definition df_sr : list sv :=
sr_set (sr_set (sr_set sr_atoms 20%bv (df_shv 23 40)) 27%bv (df_shv 23 48)) 22%bv (df_shv 23 56).

(* 24(sp) = &h->overlong and 72(sp) = &h->expected, the two frame slots the body reads. *)
Definition df_r_frame : YP09.region := YP09.mkRegion (Some 2%nat) 24 80 24 24
  [ YP09.mkChunk 24 (CVal 8 (SOff 23 56)); YP09.mkChunk 72 (CVal 8 (SOff 23 64)) ].
(* h->partial, h->npartial (8 bytes) and h->overlong (4 bytes); the body writes the last two. *)
Definition df_r_gs : YP09.region := YP09.mkRegion (Some 23%nat) 40 60 48 60
  [ YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0));
    YP09.mkChunk 56 (CVal 4 (SOff 34 0)) ].
(* the source byte at p0 + k, read through s10 = atom 26. *)
Definition df_r_src : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0
  [ YP09.mkChunk 0 (CVal 1 (SOff 35 0)) ].
Definition df_regions : smem := [ df_r_frame; df_r_gs; df_r_src ].

Definition df_HEAPF : afact := mkAF 4096 140737479966720 0.
Definition df_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0);
  (23%nat, mkAF 0x10000 0x5fb000 3); (19%nat, mkAF 1 16384 0); (25%nat, mkAF 1 16384 0);
  (24%nat, df_HEAPF); (26%nat, df_HEAPF); (32%nat, df_HEAPF);
  (33%nat, mkAF 0 6000 0); (34%nat, mkAF 0 1 0); (35%nat, mkAF 0 255 0) ] [] [].
Definition df_ss : sstate := mkSS A_dr_feed df_sr df_regions None df_facts.
(* Atom 24 (s8) is the one the shadow check SHIFTS and atom 26 (s10) the one the load reads, so the
   source byte needs an entry on both: with 24 missing the engine leaves the 0x83488 check as an
   obligation instead of deciding it (measured with a probe run of paj_run_tok). *)
Definition df_SH : list shent := [ mkSHE 23 0 96; mkSHE 24 0 1; mkSHE 26 0 1 ].
Definition df_Bx : sv := SOff 21 0.
Definition DFspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* atom 36 = &h->partial[h->npartial], the byte the ordinary arm stores (df_arm_add) *)
Definition df_extra (part np ovl b : Z) : list word := map (Z_to_bv 64) [part; np; ovl; b; part + np].

(* the shadow-address arithmetic of this walk, over atom 21 (W_drain_pro.v:458-477 is the same over 32) *)
Lemma df_U_srl : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma df_U_shadow : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (df_shv n c) = shadow_addr (v + c).
Proof.
intros E n v c Hn H21 Hv Hc. unfold df_shv, shadow_addr. rewrite U_SAlu. cbn [zalu_raw].
rewrite (df_U_srl E n v c Hn Hv Hc), (U_atom E 21 SHADOW_OFF H21) by (unfold SHADOW_OFF; lia).
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma df_den_shadow : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (df_shv n c) = w64 (shadow_addr (v + c)).
Proof.
intros E n v c Hn H21 Hv Hc.
rewrite <- (df_U_shadow E n v c Hn H21 Hv Hc). unfold U, w64. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The entry state at the loop head.  Every hypothesis is a conjunct of DRB, of DMEM's asrc_at, or a
   consequence of the placement (df_open discharges them from the cut). *)
Lemma df_feed_entry : forall (W : world SEGS) regs mem HAv pk part np ovl b nn kk,
(* The frame is above the allocator ceiling (afn_pre's stack facts, as W_drain_epi.v:235 uses them), and a
   live block ends below it: the source byte is told apart from a frame slot. *)
alloc_ceiling <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
getr regs 21 = w64 SHADOW_OFF -> getr regs 23 = w64 HAv ->
getr regs 19 = w64 nn -> getr regs 25 = w64 (nn - Z.of_nat kk) ->
getr regs 24 = w64 pk -> getr regs 26 = w64 pk ->
getr regs 20 = w64 (shadow_addr (HAv + 40)) ->
getr regs 27 = w64 (shadow_addr (HAv + 48)) ->
getr regs 22 = w64 (shadow_addr (HAv + 56)) ->
0x10000 <= HAv -> HAv + 96 <= 0x5fb000 -> HAv mod 8 = 0 ->
4096 <= pk -> pk + 1 <= alloc_ceiling -> 4096 <= part <= alloc_ceiling ->
0 <= np <= 6000 -> 0 <= ovl <= 1 -> 0 <= b <= 255 ->
1 <= nn <= 16384 -> 1 <= nn - Z.of_nat kk <= 16384 ->
(HAv + 96 <= pk \/ pk + 1 <= HAv) ->
val_mem SEGS (arm W mem) (spZ regs + 24) 8 (HAv + 56) ->
val_mem SEGS (arm W mem) (spZ regs + 72) 8 (HAv + 64) ->
val_mem SEGS (arm W mem) (HAv + 40) 8 part ->
val_mem SEGS (arm W mem) (HAv + 48) 8 np ->
val_mem SEGS (arm W mem) (HAv + 56) 4 ovl ->
val_mem SEGS (arm W mem) pk 1 b ->
(forall i, 0 <= i < 96 -> writable_at SEGS (arm W mem) (HAv + i)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (df_extra part np ovl b))) df_ss
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_feed)) mem (seg_rom SEGS))).
Proof.
intros W regs mem HAv pk part np ovl b nn kk Hsp Hal H21 H23 H19 H25 H24 H26 H20 H27 H22
  HAlo HAhi HAal Hpk Hpk1 Hpart Hnp Hovl Hb Hnn Hnk Hdisj M24 M72 M40 M48 M56 Mb HWr.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (df_extra part np ovl b))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = getr regs 2) by (exact (EEo 2%nat 2%bv eq_refl)).
assert (E21 : ew E 21 = w64 SHADOW_OFF) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E23 : ew E 23 = Z_to_bv 64 HAv) by (rewrite (EEo 23%nat 23%bv eq_refl); exact H23).
assert (E19 : ew E 19 = Z_to_bv 64 nn) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E25 : ew E 25 = Z_to_bv 64 (nn - Z.of_nat kk)) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
assert (E24 : ew E 24 = Z_to_bv 64 pk) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (E26 : ew E 26 = Z_to_bv 64 pk) by (rewrite (EEo 26%nat 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 part)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 np)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ovl)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 b)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold df_ss. apply pa_entry_st_ok_full.
- unfold df_sr.
  apply regs_ok_pin; [|intros X; discriminate X
    | rewrite H22; symmetry; apply (df_den_shadow E 23 HAv 56 E23 E21); lia].
  apply regs_ok_pin; [|intros X; discriminate X
    | rewrite H27; symmetry; apply (df_den_shadow E 23 HAv 48 E23 E21); lia].
  apply regs_ok_pin; [|intros X; discriminate X
    | rewrite H20; symmetry; apply (df_den_shadow E 23 HAv 40 E23 E21); lia].
  subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold df_regions, df_r_frame, df_r_gs, df_r_src.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 24 8 (SOff 23 56) (HAv + 56));
      [cbn [sv_denot]; rewrite E23, unsigned_lit_small by lia; reflexivity
      | zside | zside | exact M24].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 72 8 (SOff 23 64) (HAv + 64));
      [cbn [sv_denot]; rewrite E23, unsigned_lit_small by lia; reflexivity
      | zside | zside | exact M72].
  + rewrite E23, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply HWr; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (chunk_ok_val SEGS E _ HAv 40 8 (SOff 32 0) part);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | zside | zside | exact M40].
    * apply (chunk_ok_val SEGS E _ HAv 48 8 (SOff 33 0) np);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | zside | zside | exact M48].
    * apply (chunk_ok_val SEGS E _ HAv 56 4 (SOff 34 0) ovl);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | zside | zside | exact M56].
  + rewrite E26, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    * apply (chunk_ok_val SEGS E _ pk 0 1 (SOff 35 0) b);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | zside | zside |]. rewrite Z.add_0_r. exact Mb.
- apply pairwise_disjoint_of_extents.
  unfold df_regions, df_r_frame, df_r_gs, df_r_src, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Usp, E23, E26, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  change (2 ^ 47) with 140737488355328 in *.
  revert Hsp HAlo HAhi Hpk Hpk1 Hdisj C1. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [df_facts f_atoms atoms_ok]. unfold afact_ok, df_HEAPF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E21, E23, E19, E25, E24, E26, E32, E33, E34, E35,
    !unsigned_lit_small by (unfold SB, SHADOW_OFF; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 46) with 70368744177664.
  change (2 ^ 47) with 140737488355328. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hsp Hal HAlo HAhi HAal Hpk Hpk1 Hpart Hnp Hovl Hb Hnn Hnk C1. clear.
  unfold SB, SHADOW_OFF. intros.
  repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

(* The shadow entries of df_SH.  `mkSHE 23 0 96` makes every g_s field load statically covered, so the
   engine decides the `bne shadow, zero` tests at 0x83494 / 0x834a8 / 0x834d8 without leaving an
   obligation; `mkSHE 24 0 1` does the same for the source byte's check at 0x83488 and `mkSHE 26 0 1`
   for the load at 0x83490. *)
Lemma df_feed_shok : forall ly S (W : world SEGS) mem md E HAv pk q n,
AR SEGS B ly S W mem md ->
U E df_Bx = SHADOW_OFF -> U E (SOff 23 0) = HAv ->
U E (SOff 24 0) = pk -> U E (SOff 26 0) = pk ->
rg_s RG <= HAv -> HAv + 96 <= rg_s RG + 4 * ASRC ->
In (q, n) (ablocks B ly S) -> q <= pk -> pk + 1 <= q + req_size n ->
(forall x, pk <= x < pk + 1 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
sh_ok SEGS df_Bx df_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HAv pk q n HAR HBx H23 H24 H26 HAlo HAhi Hin Hq1 Hq2 Hap.
pose proof HGSB as (HGlo & HGhi & _).
assert (HSRC : forall m, U E (SOff m 0) = pk ->
  shent_ok SEGS df_Bx E (mrestrict (w_H W) mem) (mkSHE m 0 1)).
{ intros m Hm. eapply shent_ok_of_range.
  - exact (range_addressable_of_block SEGS B LAWS ly S W mem md q n pk 1 HAR Hin Hq1 Hq2).
  - exact HBx.
  - exact Hm.
  - lia.
  - lia.
  - intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
    rewrite Z.add_0_r in Hx. exact (Hap x Hx). }
unfold df_SH. constructor; [|constructor; [|constructor; [|constructor]]].
- eapply shent_ok_of_range.
  + exact (azs_range_addressable B LAWS ly S W mem md (rg_s RG) (4 * ASRC) HAR HGSZ).
  + exact HBx.
  + exact H23.
  + lia.
  + lia.
  + intros x Hx. change (Z.min 0 96) with 0 in Hx. change (Z.max 0 96) with 96 in Hx.
    unfold SHADOW_OFF. unfold ASRC in *. lia.
- exact (HSRC 24%nat H24).
- exact (HSRC 26%nat H26).
Qed.

(* ---- DRB taken apart. ----
   DRB is the cfg, the registers, the frame slots and the rest: memory and model after k bytes.  The loop's body
   moves the rest from k to S k (df_cut), then its tail 0x83544 moves the registers from k to S k (df_regs, with
   the byte counter kr); each step states only its part.  df_cut at k = dnum s1 is DE's body. *)
Definition df_regs (cx : dcx) (s1 : drain_b_c.dstate) (p0 : Z) (kr : nat) (regs1 : bvmap 5 word) : Prop :=
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 23 = w64 (dHA RG cx) /\ getr regs1 19 = w64 (dnum s1) /\
getr regs1 25 = w64 (dnum s1 - Z.of_nat kr) /\
getr regs1 26 = w64 (p0 + Z.of_nat kr) /\ getr regs1 24 = w64 (p0 + Z.of_nat kr) /\
getr regs1 20 = w64 (shadow_addr (dHA RG cx + 40)) /\ getr regs1 27 = w64 (shadow_addr (dHA RG cx + 48)) /\
getr regs1 22 = w64 (shadow_addr (dHA RG cx + 56)).

Definition df_slots (cx : dcx) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
dr_frame RG cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 32) 8 (dHA RG cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 (dHA RG cx + 56) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 (dHA RG cx + 64) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 80) 8 (shadow_addr (dHA RG cx + 16)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 (shadow_addr (dHA RG cx + 24)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (shadow_addr (dHA RG cx + 32)).

(* the allocator state (ly1, S1), the journal's step count k1, the relay entry e1 and the harness source h1 are
   parameters, so that a step states the rest at the witnesses it keeps and the source it leaves *)
Definition df_cutjh (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (p0 : Z) (ly1 : alayout)
(S1 : astate) (k1 : Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (e1 : rentry) (h1 : hsrc)
: Prop :=
exists out1 ev1 LB1 spent jb a v rs tl r0 rs0,
df_slots cx W1 m1 /\
hl_recs (hs_pending h1) = r0 :: rs0 /\ p0 = fst r0 + drain_b_c.ds_off s1 /\
0 < dnum s1 /\
bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 /\
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DSAME cx e1 h1 /\
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
hs_eintr h1 = 0 /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend s1 /\
hs_off h1 = drain_b_c.ds_off s1 /\
hs_state h1 = feed (drain_b_c.ds_ref s1) (firstn k (ddata s1)) /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1)))) /\
hl_cap (hs_expected h1) =
  pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1))) /\
DHIST cx s1 D (D ++ firstn k (ddata s1)) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
RSTART cx s1 D /\
dpfut cx s1 k jb a v rs tl /\ dbud MT MMAX cx S1 spent tl.

Definition df_cutj (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (p0 : Z) (ly1 : alayout)
(S1 : astate) (k1 : Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) : Prop :=
exists e1 h1, df_cutjh cx s1 D k p0 ly1 S1 k1 W1 m1 md1 e1 h1.

Definition df_cut (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (p0 : Z) (W1 : world SEGS)
(m1 : word -> option byte) (md1 : Model) : Prop :=
exists ly1 S1 k1, df_cutj cx s1 D k p0 ly1 S1 k1 W1 m1 md1.

Lemma df_DRB_open : forall cx s1 D k W1 c1, DRB B MT MMAX RG cx s1 D k W1 c1 ->
exists regs1 m1 md1 p0, c1 = cfg_at SEGS (BASE + A_dr_feed) regs1 m1 md1 /\ df_regs cx s1 p0 k regs1 /\
Z.of_nat k < dnum s1 /\ df_cut cx s1 D k p0 W1 m1 md1.
Proof.
intros cx s1 D k W1 c1 H.
destruct H as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & v & rs & tl &
  p0 & r0 & rs0 &
  Hcfg & R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22 &
  HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192 &
  Hpend & Hp0 & Hk & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
exists regs1, m1, md1, p0.
split; [exact Hcfg|].
split; [exact (conj R2 (conj R3 (conj R4 (conj R18 (conj R9 (conj R8 (conj R21 (conj R23 (conj R19
  (conj R25 (conj R26 (conj R24 (conj R20 (conj R27 R22))))))))))))))|].
split; [exact Hk|].
exists ly1, S1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, v, rs, tl, r0, rs0.
exact (conj (conj HFR (conj M56 (conj M64 (conj M48 (conj M200 (conj M32 (conj M24 (conj M72 (conj M80 (conj
  M40 M192)))))))))) (conj Hpend (conj Hp0 (conj Hn0 (conj Hdata (conj HMEM (conj HnoNUL (conj Hused (conj
  HSAME (conj Hcap (conj Hu (conj Hskip (conj Hkeys (conj Hka (conj Heintr (conj Hpendm (conj Hoff (conj Hstate
  (conj Hen (conj Hecap (conj HHIST (conj HRS (conj HPFUT HBUD))))))))))))))))))))))).
Qed.

Lemma df_DRB_close : forall cx s1 D k p0 W1 regs1 m1 md1,
df_regs cx s1 p0 k regs1 -> Z.of_nat k < dnum s1 -> df_cut cx s1 D k p0 W1 m1 md1 ->
DRB B MT MMAX RG cx s1 D k W1 (cfg_at SEGS (BASE + A_dr_feed) regs1 m1 md1).
Proof.
intros cx s1 D k p0 W1 regs1 m1 md1
  (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22) Hk HC.
destruct HC as (ly1 & S1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) &
  Hpend & Hp0 & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
exists regs1, ly1, S1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, v, rs, tl, p0, r0, rs0.
exact (conj eq_refl (conj R2 (conj R3 (conj R4 (conj R18 (conj R9 (conj R8 (conj R21 (conj R23 (conj R19 (conj
  R25 (conj R26 (conj R24 (conj R20 (conj R27 (conj R22 (conj HFR (conj M56 (conj M64 (conj M48 (conj M200
  (conj M32 (conj M24 (conj M72 (conj M80 (conj M40 (conj M192 (conj Hpend (conj Hp0 (conj Hk (conj Hn0 (conj
  Hdata (conj HMEM (conj HnoNUL (conj Hused (conj HSAME (conj Hcap (conj Hu (conj Hskip (conj Hkeys (conj Hka
  (conj Heintr (conj Hpendm (conj Hoff (conj Hstate (conj Hen (conj Hecap (conj HHIST (conj HRS (conj HPFUT
  HBUD)))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

Lemma df_lines_nil : forall st, lines st [] = [].
Proof. reflexivity. Qed.

Lemma df_firstn_ddata : forall s1, firstn (Z.to_nat (dnum s1)) (ddata s1) = ddata s1.
Proof. intros s1. unfold ddata. rewrite firstn_firstn, Nat.min_id. reflexivity. Qed.

Lemma df_skipn_ddata : forall s1, skipn (Z.to_nat (dnum s1)) (ddata s1) = [].
Proof.
intros s1. apply skipn_all2. unfold ddata at 1. rewrite length_firstn. lia.
Qed.

(* at k = dnum s1 every byte is fed: the rest is DE's body, with the round's pushes all done *)
Lemma df_DE_close : forall cx s1 D kr p0 W1 regs1 m1 md1,
df_regs cx s1 p0 kr regs1 -> df_cut cx s1 D (Z.to_nat (dnum s1)) p0 W1 m1 md1 ->
DE B MT MMAX RG cx s1 D W1 (cfg_at SEGS (BASE + A_dr_fed) regs1 m1 md1).
Proof.
intros cx s1 D kr p0 W1 regs1 m1 md1
  (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & _) HC.
destruct HC as (ly1 & S1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) &
  Hpend & Hp0 & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
rewrite (df_firstn_ddata s1) in Hstate, Hen, Hecap, HHIST.
unfold dpfut in HPFUT. cbv zeta in HPFUT.
rewrite (df_firstn_ddata s1), (df_skipn_ddata s1), df_lines_nil in HPFUT.
cbn [drain_b_c.pushes_run fst snd app] in HPFUT.
destruct HPFUT as (tl2 & Hdr & Htl). subst tl.
exists regs1, ly1, S1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent.
eexists. eexists. exists tl2.
exact (conj eq_refl (conj R2 (conj R3 (conj R4 (conj R18 (conj R9 (conj R8 (conj R21 (conj R23 (conj R19 (conj
  HFR (conj M56 (conj M64 (conj M48 (conj M200 (conj M32 (conj M80 (conj M40 (conj M192 (conj Hn0 (conj Hdata
  (conj HMEM (conj HnoNUL (conj Hused (conj HSAME (conj Hcap (conj Hu (conj Hskip (conj Hkeys (conj Hka (conj
  Heintr (conj Hpendm (conj Hoff (conj Hstate (conj Hen (conj Hecap (conj HHIST (conj HRS (conj Hdr
  HBUD))))))))))))))))))))))))))))))))))))))).
Qed.

(* ---- Moving DMEM to the state after a step. ----
   What each part of DMEM reads: the image's ROM, the frame [sp0 - 336, sp0), the relay entry's 56 bytes at SA
   and its blocks, g_s outside slot j, the controller's cells and g_out's block; slot j and the harness source's
   blocks are re-proved (asrc_at for the new source), and the blocks are given by the step. *)
Lemma df_bk_trans : forall (W1 W2 W3 : world SEGS) m1 m2 m3 a,
abyte_kept W1 m1 W2 m2 a -> abyte_kept W2 m2 W3 m3 a -> abyte_kept W1 m1 W3 m3 a.
Proof.
intros W1 W2 W3 m1 m2 m3 a [E1 P1] [E2 P2]. split; [rewrite E2; exact E1 | intros H; exact (P2 (P1 H))].
Qed.

Lemma df_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
length (bzs (entry_bytes e)) = 56%nat.
Proof.
intros e H1 H2. unfold bzs, entry_bytes. rewrite length_map, !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2.
reflexivity.
Qed.

(* W_drain_gs.v:671 gs_aentry_okx_kept (the drain lane's GS segment), here for this segment. *)
Lemma df_aentry_okx_kept : forall ly S W mem ly' S' W' mem' e,
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

Lemma df_dmem_rebuild : forall cx ly S W m md k e h s out ev sent LB ly' S' W' m' md' k' h',
DMEM B RG cx ly S W m md k e h s out ev sent LB ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly' S' W' m' md' k' ->
rom_view SEGS W' m' ->
apres_kept B W m W' m' -> frames S' = frames S ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
(forall a, dxSA cx <= a < dxSA cx + AENT -> abyte_kept W m W' m' a) ->
akept W m W' m' (aentry_fp e) ->
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= a < dHA RG cx + ASRC) ->
   abyte_kept W m W' m' a) ->
akept W m W' m' (aout_fp B RG (drain_b_c.ds_ocap s) out) ->
asrc_at B ly' S' W' m' (dHA RG cx) h' ->
Permutation (ablocks B ly' S')
  ((dxG cx, ATABLE) :: aentry_blks e ++ asrc_blks h' ++ aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) ->
DMEM B RG cx ly' S' W' m' md' k' e h' s out ev sent LB.
Proof.
intros cx ly S W m md k e h s out ev sent LB ly' S' W' m' md' k' h' HD HJ' KR KP KF KS KA KE KG KO HS' HP'.
destruct HD as (HJ & Hrom & Hpres & Hfr & HFR & Hent & Hawr & Hokx & Hsrc & Hoth & Hgsk & Hout & Hlive & Hperm).
assert (HIN : forall b, In b (aentry_blks e) \/ In b (aout_blks (drain_b_c.ds_ocap s) out) ->
  In b (ablocks B ly' S')).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HP'|]. right.
  destruct Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb|right].
  apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (VK : forall a n v, dsp0 cx - DRAIN_FRAME <= a -> a + Z.of_nat n <= dsp0 cx ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W' m') a n v).
{ intros a n v H1 H2 Hv. apply (akept_vm W m); [intros x Hx; apply KS; lia | exact Hv]. }
pose proof Hokx as (_ & _ & P1 & P2 & _).
split; [exact HJ'|].
split; [exact KR|].
split; [intros a H1 H2 H3 H4; exact (KP a H1 H2 H3 (Hpres a H1 H2 H3 H4))|].
split; [rewrite KF; exact Hfr|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FS).
  unfold DRAIN_FRAME in VK |- *.
  repeat split; try (apply VK; [simpl Z.of_nat; lia | simpl Z.of_nat; lia | assumption]).
  unfold dr_saved. intros i Hi. apply VK; [lia | simpl Z.of_nat; lia | exact (FS i Hi)]. }
split.
{ apply (akept_garr8 W m); [|exact Hent].
  intros x Hx. rewrite (df_entry_len e P1 P2) in Hx. apply KA. unfold AENT. simpl Z.of_nat in Hx. lia. }
split; [apply (akept_awr W m); [intros x Hx; apply KA; exact Hx | exact Hawr]|].
split; [exact (df_aentry_okx_kept ly S W m ly' S' W' m' e Hokx KE (fun b Hb => HIN b (or_introl Hb)))|].
split; [exact HS'|].
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Vo). exists f, o.
  assert (KI : forall x, rg_s RG + ASRC * Z.of_nat i <= x < rg_s RG + ASRC * Z.of_nat i + 8 ->
    abyte_kept W m W' m' x).
  { intros x Hx. apply KG; unfold dHA, ASRC in *; [lia|]. intros Hc. apply Hij. lia. }
  split; [|split; [|exact Vo]]; (apply (akept_vm W m); [intros x Hx; apply KI; simpl Z.of_nat in Hx; lia|]);
  assumption. }
split; [intros x Hx1 Hx2; exact (df_bk_trans _ _ _ _ _ _ x (Hgsk x Hx1 Hx2) (KG x Hx1 Hx2))|].
split; [exact (aout_at_kept B RG ly S W m ly' S' W' m' _ _ _ _ _ _ Hout KO (fun b Hb => HIN b (or_intror Hb)))|].
split; [exact Hlive | exact HP'].
Qed.

(* ---- A step that writes nothing the walk sees: every byte kept. ---- *)
Lemma df_kept_eq : forall (W : world SEGS) m m',
(forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) -> forall a, abyte_kept W m W m' a.
Proof.
intros W m m' Heq a. split.
- apply aview_eq_of. apply Heq.
- unfold arm, writable_at, wview. rewrite (Heq (Z_to_bv 64 a)). intros Hw. exact Hw.
Qed.

Lemma df_apres_eq : forall (H : word -> bool) m m' a,
(forall x, mrestrict H m' x = mrestrict H m x) -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Heq (Hh & b & Hb). split; [exact Hh|]. exists b.
specialize (Heq (Z_to_bv 64 a)). unfold mrestrict in Heq. rewrite Hh in Heq. rewrite Heq. exact Hb.
Qed.

Lemma df_cutj_journal : forall cx s1 D k p0 ly1 S1 k1 W m md,
df_cutj cx s1 D k p0 ly1 S1 k1 W m md ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 W m md k1.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md HC.
destruct HC as (e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 &
  _ & _ & _ & _ & _ & HMEM & _).
exact (proj1 HMEM).
Qed.

Lemma df_cutj_mem : forall cx s1 D k p0 ly1 S1 k1 W m md m' md',
df_cutj cx s1 D k p0 ly1 S1 k1 W m md ->
(forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 W m' md' k1 ->
df_cutj cx s1 D k p0 ly1 S1 k1 W m' md'.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md m' md' HC Heq HJ'.
pose proof (df_kept_eq W m m' Heq) as KA.
destruct HC as (e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) &
  Hpend & Hp0 & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
assert (VK : forall a0 n v0, val_mem SEGS (arm W m) a0 n v0 -> val_mem SEGS (arm W m') a0 n v0)
  by (intros a0 n v0 Hv; apply (akept_vm W m); [intros x _; apply KA | exact Hv]).
pose proof HMEM as (_ & Hrom & _ & _ & _ & _ & _ & _ & Hsrc & _ & _ & _ & _ & Hperm).
assert (HMEM' : DMEM B RG cx ly1 S1 W m' md' k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1).
{ apply (df_dmem_rebuild cx ly1 S1 W m md k1 e1 h1 s1 out1 ev1 _ LB1 ly1 S1 W m' md' k1 h1 HMEM HJ');
    try (intros; apply KA); try (intros ? ? ? ?; apply KA).
  - intros a0 Ha0. rewrite (proj1 (KA a0)). exact (Hrom a0 Ha0).
  - intros a0 H1 H2 H3 H4. exact (df_apres_eq (w_H W) m m' a0 Heq H4).
  - reflexivity.
  - apply (asrc_at_kept B ly1 S1 W m ly1 S1 W m' (dHA RG cx) h1 Hsrc); [intros ? ? ? ?; apply KA|].
    intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact Hperm|]. right.
    apply in_or_app. right. apply in_or_app. left. exact Hb.
  - exact Hperm. }
pose proof HMEM' as (_ & _ & _ & _ & HFR' & _).
exists e1, h1, out1, ev1, LB1, spent, jb, a, v, rs, tl, r0, rs0.
exact (conj (conj HFR' (conj (VK _ _ _ M56) (conj (VK _ _ _ M64) (conj (VK _ _ _ M48) (conj (VK _ _ _ M200)
  (conj (VK _ _ _ M32) (conj (VK _ _ _ M24) (conj (VK _ _ _ M72) (conj (VK _ _ _ M80) (conj (VK _ _ _ M40) (VK
  _ _ _ M192))))))))))) (conj Hpend (conj Hp0 (conj Hn0 (conj Hdata (conj HMEM' (conj HnoNUL (conj Hused (conj
  HSAME (conj Hcap (conj Hu (conj Hskip (conj Hkeys (conj Hka (conj Heintr (conj Hpendm (conj Hoff (conj Hstate
  (conj Hen (conj Hecap (conj HHIST (conj HRS (conj HPFUT HBUD))))))))))))))))))))))).
Qed.

Lemma df_w64_add : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity.
Qed.

Lemma df_cutj_dnum : forall cx s1 D k p0 ly1 S1 k1 W m md,
df_cutj cx s1 D k p0 ly1 S1 k1 W m md -> 0 < dnum s1 <= 16384.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md HC.
destruct HC as (e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 &
  _ & _ & _ & Hn0 & _ & HMEM & _ & _ & _ & Hcap & _).
pose proof HMEM as (_ & _ & _ & _ & _ & _ & _ & Hokx & _).
pose proof Hokx as (_ & _ & _ & _ & _ & Hc & _).
split; [exact Hn0|]. revert Hn0 Hcap Hc. clear. intros Hn0 Hcap Hc.
unfold dnum, ulen. rewrite <- Hcap. lia.
Qed.

(* the tail's register update, s9 -= 1 and s8, s10 += 1 *)
Lemma df_regs_step : forall cx s1 p0 k regs regs',
df_regs cx s1 p0 k regs ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 18 = getr regs 18 -> getr regs' 9 = getr regs 9 -> getr regs' 8 = getr regs 8 ->
getr regs' 21 = getr regs 21 -> getr regs' 23 = getr regs 23 -> getr regs' 19 = getr regs 19 ->
getr regs' 20 = getr regs 20 -> getr regs' 27 = getr regs 27 -> getr regs' 22 = getr regs 22 ->
getr regs' 25 = Z_to_bv 64 (bv_unsigned (getr regs 25) + -1) ->
getr regs' 26 = Z_to_bv 64 (bv_unsigned (getr regs 26) + 1) ->
getr regs' 24 = Z_to_bv 64 (bv_unsigned (getr regs 24) + 1) ->
df_regs cx s1 p0 (S k) regs'.
Proof.
intros cx s1 p0 k regs regs' (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22)
  E2 E3 E4 E18 E9 E8 E21 E23 E19 E20 E27 E22 E25 E26 E24.
unfold df_regs. unfold spZ in *.
split; [rewrite E2; exact R2|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
split; [rewrite E18; exact R18|]. split; [rewrite E9; exact R9|].
split; [rewrite E8; exact R8|]. split; [rewrite E21; exact R21|].
split; [rewrite E23; exact R23|]. split; [rewrite E19; exact R19|].
split; [rewrite E25, R25; unfold w64; rewrite df_w64_add; f_equal; lia|].
split; [rewrite E26, R26; unfold w64; rewrite df_w64_add; f_equal; lia|].
split; [rewrite E24, R24; unfold w64; rewrite df_w64_add; f_equal; lia|].
split; [rewrite E20; exact R20|]. split; [rewrite E27; exact R27|]. rewrite E22; exact R22.
Qed.

(* ---- What the body reads at the loop head, from the cut. ---- *)
Lemma df_nth_error_firstn : forall {A} (l : list A) n i x, nth_error (firstn n l) i = Some x -> nth_error l i = Some x.
Proof.
intros A l n. revert l. induction n as [|n IH]; intros l i x H.
- cbn in H. destruct i; discriminate.
- destruct l as [|y l]; [cbn in H; destruct i; discriminate|].
  destruct i as [|i]; cbn in H |- *; [exact H | exact (IH l i x H)].
Qed.

Lemma df_nth_error_skipn : forall {A} (l : list A) n i x, nth_error (skipn n l) i = Some x -> nth_error l (n + i) = Some x.
Proof.
intros A l n. revert l. induction n as [|n IH]; intros l i x H.
- exact H.
- destruct l as [|y l]; cbn in H |- *.
  + destruct i; discriminate.
  + exact (IH l i x H).
Qed.

(* data byte k is the byte at p0 + k, in the head pending text's block (a block other than h->partial) *)
Lemma df_src_byte : forall cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b,
df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
exists q qn, In (q, qn) (ablocks B ly1 S1) /\ In (q, qn) (asrc_blks h1) /\ q <> hs_partial h1 /\
q <= p0 + Z.of_nat k /\ p0 + Z.of_nat k + 1 <= q + req_size qn /\
val_mem SEGS (arm W m) (p0 + Z.of_nat k) 1 b /\ 0 <= b < 256.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b HC Hb.
destruct HC as (out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 &
  _ & Hpend & Hp0 & _ & _ & HMEM & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpendm & Hoff & _).
pose proof HMEM as (_ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _ & _ & _ & _ & Hperm).
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Apend & _ & _ & _ & _ & Ahead & _ & _ & _ & _ & _ & _ &
  _ & _ & Anod).
pose proof Apend as (_ & _ & _ & _ & _ & _ & _ & _ & Arecs).
rewrite Hpend in Arecs. apply Forall_inv in Arecs as (Rin & Rg & _ & _).
assert (Hoff0 : 0 <= hs_off h1 < Z.of_nat (length (snd r0))).
{ clear - Ahead Hpend. destruct Ahead as [(Hn & _) | (r & rs' & Hr & Ho)].
  { rewrite Hpend in Hn. discriminate. }
  rewrite Hpend in Hr.
  injection Hr as -> ->. exact Ho. }
unfold ddata, dhead in Hb. rewrite <- Hpendm, Hpend in Hb. cbn [map] in Hb.
apply df_nth_error_firstn in Hb. apply df_nth_error_skipn in Hb.
remember (Z.to_nat (drain_b_c.ds_off s1) + k)%nat as j eqn:Hjdef.
assert (Hj : (j < length (snd r0))%nat).
{ assert (Hne : nth_error (bzs (snd r0)) j <> None) by (rewrite Hb; discriminate).
  apply nth_error_Some in Hne. unfold bzs in Hne. rewrite length_map in Hne. exact Hne. }
assert (Hnth : nth j (bzs (snd r0 ++ [Z_to_bv 8 0])) 0 = b).
{ unfold bzs. rewrite map_app, app_nth1 by (rewrite length_map; exact Hj).
  apply nth_error_nth. exact Hb. }
assert (Hlen : (j < length (bzs (snd r0 ++ [Z_to_bv 8 0])))%nat)
  by (unfold bzs; rewrite length_map, length_app; cbn [length]; clear - Hj; lia).
destruct (Rg j Hlen) as (Hv & Hr). rewrite Hnth in Hv, Hr.
assert (Haddr : fst r0 + Z.of_nat j = p0 + Z.of_nat k)
  by (rewrite Hp0, Hjdef; clear - Hoff Hoff0; lia).
rewrite Haddr in Hv.
exists (fst r0), (Z.of_nat (length (snd r0)) + 1).
split; [exact Rin|].
split.
{ unfold asrc_blks, alist_blks. right. apply in_or_app. left. apply in_or_app. right.
  rewrite Hpend. left. reflexivity. }
split.
{ intros Heq. unfold hs_blocks in Anod. cbn [app] in Anod.
  apply (NoDup_remove_2 _ _ _ (proj1 (NoDup_ListNoDup _) Anod)). apply in_or_app. left.
  unfold list_blocks. apply in_or_app. right. rewrite Hpend. left. exact Heq. }
pose proof (req_size_pos (Z.of_nat (length (snd r0)) + 1) ltac:(clear; lia)) as (_ & Hrq).
split; [rewrite Hp0; clear - Hoff Hoff0; lia|].
split; [rewrite <- Haddr; clear - Hj Hrq; lia|].
split; [exact Hv | exact Hr].
Qed.

(* the symbolic state at the loop head and its shadow entries, from the cut *)
Lemma df_entry_full : forall cx s1 D k p0 ly1 S1 k1 W regs m md e1 h1 b,
DBASE B MT MMAX RG cx -> df_regs cx s1 p0 k regs -> Z.of_nat k < dnum s1 ->
df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (df_extra (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b))) df_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_feed)) m (seg_rom SEGS))) /\
sh_ok SEGS df_Bx df_SH (Eimg (Ereg regs (df_extra (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b)))
  (mrestrict (w_H W) m).
Proof.
intros cx s1 D k p0 ly1 S1 k1 W regs m md e1 h1 b HB HR Hk HC Hb.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HGSB as (HGlo & HGhi & HGal).
pose proof HR as (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
destruct (df_src_byte cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b HC Hb)
  as (q & qn & Hqin & _ & _ & Hq1 & Hq2 & Mb & Hb8).
pose proof (df_cutj_dnum cx s1 D k p0 ly1 S1 k1 W m md (ex_intro _ e1 (ex_intro _ h1 HC))) as Hn.
destruct HC as (out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) & _ & _ & _ & _ & HMEM & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _).
assert (HAR : AR SEGS B ly1 S1 W m md) by (eapply ajournal_gx_AR; exact HJ).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK = 16848) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
pose proof Hsrc as (_ & _ & _ & _ & Aawr & _ & _ & _ & _ & _ & _ & M40' & M48' & M56' & _ & Anp & Aovl & Apb & _).
destruct (al_blocks SEGS B LAWS ly1 S1 W m md q qn HAR Hqin) as (_ & Hq4096 & Hqceil & Hqapp & _).
destruct (al_blocks SEGS B LAWS ly1 S1 W m md _ _ HAR Apb) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos qn ltac:(destruct (al_blocks SEGS B LAWS ly1 S1 W m md q qn HAR Hqin)
  as (_ & _ & _ & _ & _ & _ & Hqn); lia)) as (Hrq1 & _).
pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrp).
set (HA := dHA RG cx) in *. set (pk := p0 + Z.of_nat k) in *.
assert (HAe : HA = rg_s RG + ASRC * Z.of_nat (dxj cx)) by reflexivity.
assert (HAlo : rg_s RG <= HA) by (rewrite HAe; unfold ASRC; lia).
assert (HAhi : HA + ASRC <= rg_s RG + 4 * ASRC) by (rewrite HAe; unfold ASRC; lia).
assert (HAal : HA mod 8 = 0).
{ rewrite HAe. unfold ASRC. replace (rg_s RG + 96 * Z.of_nat (dxj cx)) with (rg_s RG + Z.of_nat (dxj cx) * 12 * 8) by lia.
  rewrite Z.mod_add by lia. exact HGal. }
assert (Hdisj : HA + 96 <= pk \/ pk + 1 <= HA).
{ destruct (Z_lt_le_dec pk HA) as [Hlt|Hge]; [right; lia|].
  destruct (Z_lt_le_dec pk (HA + 96)) as [Hlt2|Hge2]; [|left; lia].
  exfalso. apply (blk_img SEGS B LAWS ly1 S1 W m md q qn pk HAR Hqin ltac:(lia)).
  apply (HG pk). unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold ASRC in *. lia. }
assert (Hsp : alloc_ceiling <= spZ regs <= 2 ^ 47) by (rewrite R2; lia).
assert (Hsp16 : spZ regs mod 16 = 0).
{ rewrite R2, HDF. replace (dsp0 cx - 336) with (dsp0 cx + (-21) * 16) by lia. rewrite Z.mod_add by lia.
  exact Hal16. }
split.
- apply (df_feed_entry W regs m HA pk (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b (dnum s1) k
    Hsp Hsp16 R21 R23 R19 R25 R24 R26 R20 R27 R22 ltac:(lia) ltac:(unfold ASRC in *; lia) HAal
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold APARTIAL in *; lia) ltac:(destruct Aovl; lia) ltac:(lia)
    ltac:(lia) ltac:(lia) Hdisj).
  + rewrite R2. exact M24.
  + rewrite R2. exact M72.
  + exact M40'.
  + exact M48'.
  + exact M56'.
  + exact Mb.
  + intros i Hi. apply Aawr. unfold ASRC. exact Hi.
- set (E := Eimg (Ereg regs (df_extra (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b))).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
  { intros n r Hn'. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn'. }
  apply (df_feed_shok ly1 S1 W m md E HA pk q qn HAR).
  + unfold df_Bx. apply U_atom; [rewrite (EE 21%nat 21%bv eq_refl); exact R21 | unfold SHADOW_OFF; lia].
  + apply U_atom; [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia].
  + apply U_atom; [rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia].
  + apply U_atom; [rewrite (EE 26%nat 26%bv eq_refl); exact R26 | lia].
  + exact HAlo.
  + unfold ASRC in *. lia.
  + exact Hqin.
  + exact Hq1.
  + exact Hq2.
  + intros x Hx. revert Hqapp Hq1 Hq2 Hx Hrq1. clear.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.

(* "the run left the walk's view of memory as it was": a run over a state whose regions have no window *)
Ltac df_meq MEQ :=
lazymatch goal with H : frame_of _ _ (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- _ =>
  assert (MEQ : forall x, mrestrict Hh m1 x = mrestrict Hh m0 x)
    by (intros x; apply H; intros (r & Hin & _); cbn in Hin; destruct Hin)
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* ---- The loop's tail, 0x83544: s9 -= 1, s8 += 1, s10 += 1, then the back edge to DRB (S k) or the exit to
   DE.  It reads and writes no memory: the state's symbolic memory is empty. ---- *)
Definition A_df_tail : Z := AF_fr_drain + 0x468.
Definition df_tss : sstate := mkSS A_df_tail sr_atoms [] None (mkFacts [ (21%nat, mkAF SB SB 0) ] [] []).

Lemma df_tail : forall cx s1 D k p0 W regs m md Q,
df_regs cx s1 p0 k regs -> df_cut cx s1 D (S k) p0 W m md -> Z.of_nat (S k) <= dnum s1 ->
(forall W2 c2, DRB B MT MMAX RG cx s1 D (S k) W2 c2 -> SRr SEGS W2 c2 Q) ->
(forall W2 c2, DE B MT MMAX RG cx s1 D W2 c2 -> SRr SEGS W2 c2 Q) ->
SRr SEGS W (cfg_at SEGS (BASE + A_df_tail) regs m md) Q.
Proof.
intros cx s1 D k p0 W regs m md Q HR HC Hle Hnext Hend.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22).
destruct HC as (ly1 & S1 & k1 & HC).
pose proof (df_cutj_journal _ _ _ _ _ _ _ _ _ _ _ HC) as HJ.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HS : st_ok_pi SEGS VAL E df_tss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_df_tail)) m (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold df_tss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint]. exact I.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE 21%nat 21%bv eq_refl), R21. unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
    repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS (SOff 21 0) [] E (mrestrict (w_H W) m)) by constructor.
clear HE.
unfold cfg_at.
paj_run_tok RUN HS HJ SHOK DFspan. { apply awr_ok_x_of0. awr_ok_tac. }
df_meq MEQ1.
pose proof (df_cutj_dnum _ _ _ _ _ _ _ _ _ _ _ HC) as (Hn0 & Hn16).
assert (E25 : ew E 25 = Z_to_bv 64 (dnum s1 - Z.of_nat k)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (U25 : U E (SOff 25 (-1)) = dnum s1 - Z.of_nat k + -1) by (apply U_atom_off; [exact E25 | lia | lia]).
assert (U0 : U E (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
psrr_branch_tok RUN BR HS SHOK DFspan.
- (* the back edge 0x83550 -> 0x8347c: a byte is left *)
  rewrite branch_ne_U, U25, U0 in Hc.
  assert (Hlt : Z.of_nat (S k) < dnum s1)
    by (destruct (Z.eqb_spec (dnum s1 - Z.of_nat k + -1) 0); [discriminate | lia]).
  paj_run_to_tok RUNTO HS HJ SHOK DFspan A_dr_feed. { apply awr_ok_x_of0. awr_ok_tac. }
  df_meq MEQ2.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (18%bv : bv 5) Q18. prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8.
  prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (19%bv : bv 5) Q19.
  prreg HS (20%bv : bv 5) Q20. prreg HS (27%bv : bv 5) Q27. prreg HS (22%bv : bv 5) Q22.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (24%bv : bv 5) Q24.
  apply Hnext.
  apply (df_DRB_close cx s1 D (S k) p0 W).
  + apply (df_regs_step cx s1 p0 k regs _ HR).
    * rewrite Q2. exact (EE 2%nat 2%bv eq_refl).
    * rewrite Q3. exact (EE 3%nat 3%bv eq_refl).
    * rewrite Q4. exact (EE 4%nat 4%bv eq_refl).
    * rewrite Q18. exact (EE 18%nat 18%bv eq_refl).
    * rewrite Q9. exact (EE 9%nat 9%bv eq_refl).
    * rewrite Q8. exact (EE 8%nat 8%bv eq_refl).
    * rewrite Q21. exact (EE 21%nat 21%bv eq_refl).
    * rewrite Q23. exact (EE 23%nat 23%bv eq_refl).
    * rewrite Q19. exact (EE 19%nat 19%bv eq_refl).
    * rewrite Q20. exact (EE 20%nat 20%bv eq_refl).
    * rewrite Q27. exact (EE 27%nat 27%bv eq_refl).
    * rewrite Q22. exact (EE 22%nat 22%bv eq_refl).
    * rewrite Q25, (EE 25%nat 25%bv eq_refl). reflexivity.
    * rewrite Q26, (EE 26%nat 26%bv eq_refl). reflexivity.
    * rewrite Q24, (EE 24%nat 24%bv eq_refl). reflexivity.
  + exact Hlt.
  + exists ly1, S1, k1. apply (df_cutj_mem cx s1 D (S k) p0 ly1 S1 k1 W m md _ _ HC); [|exact HJ].
    intros x. rewrite MEQ2, MEQ1. reflexivity.
- (* the exit 0x83554 -> 0x835ac: the round's bytes are all fed *)
  rewrite branch_ne_U, U25, U0 in Hc.
  assert (Heq : Z.to_nat (dnum s1) = S k)
    by (destruct (Z.eqb_spec (dnum s1 - Z.of_nat k + -1) 0); [lia | discriminate]).
  paj_run_to_tok RUNTO HS HJ SHOK DFspan A_dr_fed. { apply awr_ok_x_of0. awr_ok_tac. }
  df_meq MEQ2.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (18%bv : bv 5) Q18. prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8.
  prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (19%bv : bv 5) Q19.
  prreg HS (20%bv : bv 5) Q20. prreg HS (27%bv : bv 5) Q27. prreg HS (22%bv : bv 5) Q22.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (24%bv : bv 5) Q24.
  apply Hend.
  apply (df_DE_close cx s1 D (S k) p0 W).
  + apply (df_regs_step cx s1 p0 k regs _ HR).
    * rewrite Q2. exact (EE 2%nat 2%bv eq_refl).
    * rewrite Q3. exact (EE 3%nat 3%bv eq_refl).
    * rewrite Q4. exact (EE 4%nat 4%bv eq_refl).
    * rewrite Q18. exact (EE 18%nat 18%bv eq_refl).
    * rewrite Q9. exact (EE 9%nat 9%bv eq_refl).
    * rewrite Q8. exact (EE 8%nat 8%bv eq_refl).
    * rewrite Q21. exact (EE 21%nat 21%bv eq_refl).
    * rewrite Q23. exact (EE 23%nat 23%bv eq_refl).
    * rewrite Q19. exact (EE 19%nat 19%bv eq_refl).
    * rewrite Q20. exact (EE 20%nat 20%bv eq_refl).
    * rewrite Q27. exact (EE 27%nat 27%bv eq_refl).
    * rewrite Q22. exact (EE 22%nat 22%bv eq_refl).
    * rewrite Q25, (EE 25%nat 25%bv eq_refl). reflexivity.
    * rewrite Q26, (EE 26%nat 26%bv eq_refl). reflexivity.
    * rewrite Q24, (EE 24%nat 24%bv eq_refl). reflexivity.
  + rewrite Heq. exists ly1, S1, k1. apply (df_cutj_mem cx s1 D (S k) p0 ly1 S1 k1 W m md _ _ HC); [|exact HJ].
    intros x. rewrite MEQ2, MEQ1. reflexivity.
Qed.

(* ---- The cut after one byte, from the state the body leaves at 0x83544. ----
   What the body keeps is stated so that the statement names no witness of the cut.  The arms that push nothing
   run only the program: every byte outside the fields they write (h->npartial, h->overlong) and the partial
   buffer is kept.  The push keeps what its callee's journal keeps: every live block other than the expected
   list's vector, every image byte outside list_push's globals that is not an allocator static or errno, and the
   frame.  The blocks are separate because the cut's block list is a permutation of the allocator's live blocks
   (DMEM), and AR_sep makes the blocks pairwise disjoint. *)

(* pairwise over a map, over a permutation, and across the two halves of an append *)
Lemma df_pw_map : forall {X Y : Type} (R : Y -> Y -> Prop) (f : X -> Y) (l : list X),
pairwise R (map f l) -> pairwise (fun x y => R (f x) (f y)) l.
Proof.
intros X Y R f l. induction l as [|x l IH]; cbn [map pairwise]; intros H; [exact I|].
destruct H as [Hf Hp]. split; [rewrite Forall_map in Hf; exact Hf | exact (IH Hp)].
Qed.

Lemma df_pw_perm : forall {X : Type} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros X R Hs l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
- exact I.
- cbn [pairwise] in H |- *. destruct H as [Hf Hp]. split; [|exact (IH Hp)].
  rewrite Forall_forall in Hf |- *. intros z Hz. apply Hf.
  exact (Permutation_in _ (Permutation_sym HP) Hz).
- cbn [pairwise] in H |- *. destruct H as [Hf1 [Hf2 Hp]].
  split; [constructor; [apply Hs; exact (Forall_inv Hf1) | exact Hf2]|].
  split; [exact (Forall_inv_tail Hf1) | exact Hp].
- exact (IH2 (IH1 H)).
Qed.

Lemma df_pw_app : forall {X : Type} (R : X -> X -> Prop) l1 l2 x y,
pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1 l2 x y. induction l1 as [|z l1 IH]; intros H Hx Hy; [destruct Hx|].
cbn [app pairwise] in H. destruct H as [Hf Hp]. destruct Hx as [<- | Hx]; [|exact (IH Hp Hx Hy)].
rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. exact Hy.
Qed.

Lemma df_zdisj_sym : forall x y, zdisjoint (block_rng x) (block_rng y) -> zdisjoint (block_rng y) (block_rng x).
Proof. intros x y [H|H]; [right | left]; exact H. Qed.

Lemma df_pw_blocks : forall ly S (W : world SEGS) m md, AR SEGS B ly S W m md ->
pairwise (fun x y => zdisjoint (block_rng x) (block_rng y)) (ablocks B ly S).
Proof.
intros ly S W m md HAR.
destruct (al_sep _ _ LAWS ly S W m md HAR) as [Hsep _].
destruct (pairwise_app_l _ _ _ Hsep) as [Hb _].
exact (df_pw_map zdisjoint block_rng (ablocks B ly S) Hb).
Qed.

(* a heap block holds no byte of g_s (blocks are not in the image, g_s is: HG) *)
Lemma df_blk_gs : forall ly S (W : world SEGS) m md p n x,
AR SEGS B ly S W m md -> In (p, n) (ablocks B ly S) -> p <= x < p + n ->
~ (rg_s RG <= x < rg_s RG + 4 * ASRC).
Proof.
intros ly S W m md p n x HAR Hin Hx Hg.
destruct (al_blocks SEGS B LAWS ly S W m md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq).
apply (blk_img SEGS B LAWS ly S W m md p n x HAR Hin ltac:(lia)).
apply (proj1 (HG x ltac:(unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia))).
Qed.

(* two live blocks at different addresses share no byte *)
Lemma df_blk_out : forall ly S (W : world SEGS) m md p n q k x,
AR SEGS B ly S W m md -> In (p, n) (ablocks B ly S) -> In (q, k) (ablocks B ly S) -> p <> q ->
p <= x < p + n -> ~ (q <= x < q + k).
Proof.
intros ly S W m md p n q k x HAR Hp Hq Hne Hx Hy.
destruct (al_blocks SEGS B LAWS ly S W m md p n HAR Hp) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (al_blocks SEGS B LAWS ly S W m md q k HAR Hq) as (_ & _ & _ & _ & _ & _ & Hk).
pose proof (req_size_pos n ltac:(lia)) as (_ & Rn). pose proof (req_size_pos k ltac:(lia)) as (_ & Rk).
pose proof (df_pw_blocks ly S W m md HAR) as Hpw.
assert (Hne2 : (p, n) <> (q, k)) by (intros E; injection E as E1 _; exact (Hne E1)).
destruct (in_split_2 (p, n) (q, k) _ Hp Hq Hne2) as (l1 & l2 & l3 & [E|E]);
  pose proof (pairwise_In2 _ _ _ _ l1 l2 l3 Hpw E) as D; unfold zdisjoint, block_rng in D; cbn [fst snd] in D;
  revert Hx Hy Rn Rk D; clear; intros; lia.
Qed.

(* a byte of a live block is an address: the block lies in [4096, alloc_ceiling) *)
Lemma df_blk_rng : forall ly S (W : world SEGS) m md p n x,
AR SEGS B ly S W m md -> In (p, n) (ablocks B ly S) -> p <= x < p + n -> 0 <= x < 2 ^ 64.
Proof.
intros ly S W m md p n x HAR Hin Hx.
destruct (al_blocks SEGS B LAWS ly S W m md p n HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos n (proj1 Hn)) as (_ & Rn).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
revert Hx H4 Hc Rn ACL. clear. intros. lia.
Qed.

(* the bytes after the k-th: skipn k d = nth k d :: skipn (S k) d *)
Lemma df_skipn_nth : forall {A} (l : list A) n x, nth_error l n = Some x -> skipn n l = x :: skipn (S n) l.
Proof.
intros A l. induction l as [|y l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
destruct n as [|n]; cbn [nth_error skipn] in *.
- injection Hn as <-. reflexivity.
- exact (IH n x Hn).
Qed.

Lemma df_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|kk ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

(* the list footprints: blocks named by a list, and the list kept from its header and its blocks *)
Lemma df_alist_blks_fst : forall l, map fst (alist_blks l) = list_blocks l.
Proof.
intros l. unfold alist_blks, list_blocks. rewrite map_app, map_map. destruct (hl_cap l =? 0); reflexivity.
Qed.

Lemma df_alist_blks_in : forall ly S (W : world SEGS) m LA l lines,
alist_at B ly S W m LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros ly S W m LA l lines (_ & _ & _ & _ & _ & H6 & _ & _ & H9) b Hb.
unfold alist_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0 | Hc0]; cbn [In] in Hb; [destruct Hb|].
  destruct Hb as [<- | []].
  destruct H6 as [(Hc & _) | (_ & Hin & _)]; [exfalso; exact (Hc0 Hc) | exact Hin].
- apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in H9. exact (proj1 (H9 r Hr)).
Qed.

Lemma df_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma df_alist_upd : forall ly S (W : world SEGS) m m' LA l lines,
alist_at B ly S W m LA l lines ->
(forall x, LA <= x < LA + 16 -> abyte_kept W m W m' x) ->
(forall p n x, In (p, n) (alist_blks l) -> p <= x < p + n -> abyte_kept W m W m' x) ->
alist_at B ly S W m' LA l lines.
Proof.
intros ly S W m m' LA l lines HL KH KB.
pose proof HL as (_ & _ & _ & _ & _ & Hv & _ & _ & _).
apply (alist_at_kept B ly S W m ly S W m' LA l lines HL); [|exact (df_alist_blks_in ly S W m LA l lines HL)].
intros r Hr a Ha. unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- apply KH. cbn [fst snd] in Ha. lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0 | Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, df_recs_len in Ha.
    destruct Hv as [(Hc & _) | (Hc & _ & Hj & _)]; [exfalso; exact (Hc0 Hc)|].
    apply (KB (hl_v l) (AREC * hl_cap l)).
    * unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
    * unfold hl_n, AREC in *. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (KB (fst q) (Z.of_nat (length (snd q)) + 1)); [| lia].
    unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
Qed.

(* writable_at reads the memory only through the byte's presence (W_relay_event.v re_wr_pres) *)
Lemma df_wr_pres : forall (W : world SEGS) (m m' : word -> option byte) a,
(forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W) m') a.
Proof.
intros W m m' a Hp Hw. apply (writable_at_grows SEGS (mrestrict (w_H W) m) (mrestrict (w_H W) m') a); [|exact Hw].
intros x Hx. unfold mrestrict in Hx |- *.
destruct (w_H W x) eqn:Hh; [exfalso; exact (Hx eq_refl)|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
destruct (Hp (bv_unsigned x)) as [Hh' [b' Hb']].
{ split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Em]. }
rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

Lemma df_sep_perm : forall ly S (W : world SEGS) m md (L : list (Z * Z)),
AR SEGS B ly S W m md -> Permutation (ablocks B ly S) L ->
pairwise (fun x y => zdisjoint (block_rng x) (block_rng y)) L.
Proof.
intros ly S W m md L HAR HP.
exact (df_pw_perm _ df_zdisj_sym _ _ HP (df_pw_blocks ly S W m md HAR)).
Qed.

(* the harness source after a byte that pushes nothing: only h->npartial, h->overlong and the partial buffer
   changed *)
Lemma df_asrc_upd : forall ly S (W : world SEGS) m md m' HA h1 h2,
AR SEGS B ly S W m md -> asrc_at B ly S W m HA h1 ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 48 <= a < HA + 60) -> ~ (hs_partial h1 <= a < hs_partial h1 + APARTIAL) ->
   abyte_kept W m W m' a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
val_mem SEGS (arm W m') (HA + 48) 8 (hs_npartial h2) -> val_mem SEGS (arm W m') (HA + 56) 4 (hs_overlong h2) ->
0 <= hs_npartial h2 <= APARTIAL -> (hs_overlong h2 = 0 \/ hs_overlong h2 = 1) ->
Z.of_nat (length (hs_pjunk h2)) = APARTIAL -> garr8 SEGS (arm W m') (hs_partial h1) (bzs (hs_pjunk h2)) ->
~ In (Z_to_bv 8 0) (hs_W h2) ->
hs_fd h2 = hs_fd h1 -> hs_open h2 = hs_open h1 -> hs_closed h2 = hs_closed h1 -> hs_eintr h2 = hs_eintr h1 ->
hs_pending h2 = hs_pending h1 -> hs_off h2 = hs_off h1 -> hs_partial h2 = hs_partial h1 ->
hs_expected h2 = hs_expected h1 -> hs_held h2 = hs_held h1 ->
asrc_at B ly S W m' HA h2.
Proof.
intros ly S W m md m' HA h1 h2 HAR HS HAlo HAhi KP Hpres V48 V56 Hnp2 Hov2 Hlen2 Hg2 HW2
  Efd Eop Ecl Eei Epe Eoff Epa Eex Ehe.
pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & H24).
(* slot j outside [HA + 48, HA + 60) is kept: it is image, the partial buffer is a heap block *)
assert (KH : forall x, HA <= x < HA + ASRC -> ~ (HA + 48 <= x < HA + 60) -> abyte_kept W m W m' x).
{ intros x Hx Hn. apply KP; [|exact Hn|].
  - pose proof HGSB as (G1 & G2 & _). revert Hx HAlo HAhi G1 G2. clear. unfold ASRC. intros. lia.
  - intros Hp. exact (df_blk_gs ly S W m md (hs_partial h1) APARTIAL x HAR H18 Hp ltac:(lia)). }
assert (VH : forall a n v, HA <= a -> a + Z.of_nat n <= HA + 48 ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v).
{ intros a n v Ha Hn Hv. apply (akept_vm W m); [|exact Hv]. intros x Hx. apply KH; unfold ASRC; lia. }
(* the three lists' blocks are not the partial buffer (NoDup (hs_blocks h1)) *)
assert (NP : forall p, In p (list_blocks (hs_pending h1)) \/ In p (list_blocks (hs_expected h1)) \/
  In p (list_blocks (hs_held h1)) -> p <> hs_partial h1).
{ intros p Hp Ep. subst p.
  assert (HN : NoDup (list_blocks (hs_pending h1) ++ hs_partial h1 ::
    (list_blocks (hs_expected h1) ++ list_blocks (hs_held h1)))) by exact H24.
  apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HN. apply List.NoDup_remove_2 in HN. apply HN.
  destruct Hp as [Hp | [Hp | Hp]]; apply in_or_app;
    [left; exact Hp | right; apply in_or_app; left; exact Hp | right; apply in_or_app; right; exact Hp]. }
assert (LK : forall LA l lines, HA + 16 <= LA -> LA + 16 <= HA + ASRC -> (LA + 16 <= HA + 48 \/ HA + 60 <= LA) ->
  (forall p, In p (list_blocks l) -> p <> hs_partial h1) ->
  alist_at B ly S W m LA l lines -> alist_at B ly S W m' LA l lines).
{ intros LA l lines HL1 HL2 HL3 Hnp HL. apply (df_alist_upd ly S W m m' LA l lines HL).
  - intros x Hx. apply KH; lia.
  - intros p n x Hpn Hx.
    pose proof (df_alist_blks_in ly S W m LA l lines HL (p, n) Hpn) as Hin.
    apply KP; [exact (df_blk_rng ly S W m md p n x HAR Hin Hx) | |].
    + intros Hc. exact (df_blk_gs ly S W m md p n x HAR Hin Hx ltac:(unfold ASRC in *; lia)).
    + apply (df_blk_out ly S W m md p n (hs_partial h1) APARTIAL x HAR Hin H18); [|exact Hx].
      apply Hnp. rewrite <- df_alist_blks_fst. exact (in_map fst (alist_blks l) (p, n) Hpn). }
assert (AW : awr W m' HA ASRC).
{ intros i Hi. apply (df_wr_pres W m m' (HA + i) Hpres). exact (H5 i Hi). }
unfold asrc_at, hs_blocks. rewrite Efd, Eop, Ecl, Eei, Epe, Eoff, Epa, Eex, Ehe.
split; [apply VH; [lia | cbn; lia | exact H1]|].
split; [apply VH; [lia | cbn; lia | exact H2]|].
split; [apply VH; [lia | cbn; lia | exact H3]|].
split; [apply VH; [lia | cbn; lia | exact H4]|].
split; [exact AW|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
split; [apply (LK (HA + 16) _ false); [lia | unfold ASRC; lia | lia
  | intros p Hp; apply NP; left; exact Hp | exact H10]|].
split; [apply VH; [lia | cbn; lia | exact H11]|].
split; [apply VH; [lia | cbn; lia | exact H12]|].
split; [exact V48|]. split; [exact V56|].
split; [exact H15|]. split; [exact Hnp2|]. split; [exact Hov2|]. split; [exact H18|].
split; [exact Hlen2|]. split; [exact Hg2|]. split; [exact HW2|].
split; [apply (LK (HA + 64) _ true); [lia | unfold ASRC; lia | lia
  | intros p Hp; apply NP; right; left; exact Hp | exact H22]|].
split; [apply (LK (HA + 80) _ true); [lia | unfold ASRC; lia | lia
  | intros p Hp; apply NP; right; right; exact Hp | exact H23]|].
exact H24.
Qed.

(* skip, long, add, reset: the byte b pushes no line *)
Lemma df_close_local : forall cx s1 D k p0 ly1 S1 k1 W m md e1 h1 m' md' h2 b,
DBASE B MT MMAX RG cx ->
df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 W m' md' k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) ->
   ~ (hs_partial h1 <= a < hs_partial h1 + APARTIAL) -> abyte_kept W m W m' a) ->
(forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_client RG <= a < rg_client RG + 4) \/
   (rg_send_dead RG <= a < rg_send_dead RG + 1) -> abyte_kept W m W m' a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
asrc_at B ly1 S1 W m' (dHA RG cx) h2 ->
nth_error (ddata s1) k = Some b ->
hs_state h2 = fst (step (hs_state h1) b) -> snd (step (hs_state h1) b) = None ->
hs_fd h2 = hs_fd h1 -> hs_open h2 = hs_open h1 -> hs_closed h2 = hs_closed h1 -> hs_eintr h2 = hs_eintr h1 ->
hs_pending h2 = hs_pending h1 -> hs_off h2 = hs_off h1 -> hs_partial h2 = hs_partial h1 ->
hs_expected h2 = hs_expected h1 -> hs_held h2 = hs_held h1 ->
df_cutjh cx s1 D (S k) p0 ly1 S1 k1 W m' md' e1 h2.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md e1 h1 m' md' h2 b HB HC HJ' KP KC Hpres HS2 Hb Hst Hnone
  Efd Eop Ecl Eei Epe Eoff Epa Eex Ehe.
destruct HC as (out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) &
  Hpend & Hp0 & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
pose proof HB as (_ & _ & _ & HGSA & HSAG & _ & _ & _ & Hj & _).
pose proof HMEM as (HJ & Hrom & _ & _ & _ & _ & _ & Hokx & Hsrc & _ & _ & _ & _ & Hperm).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hslo, Hshi.
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H18 & _).
pose proof HGSB as (HGlo & HGhi & _).
pose proof (proj1 (proj1 (@YM05.alloc_ceiling_value rc))) as ACV.
assert (HDS : DRAIN_STK = 16848) by reflexivity.
assert (RQP : req_size APARTIAL = APARTIAL) by reflexivity.
assert (RQT : req_size ATABLE = ATABLE) by reflexivity.
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC)
  by (revert Hj; clear; unfold dHA, ASRC; intros; lia).
destruct (al_blocks SEGS B LAWS ly1 S1 W m md (hs_partial h1) APARTIAL HAR H18) as (_ & _ & Hpc & _).
(* image bytes are not in the partial buffer (a heap block) *)
assert (IMP : forall x, in_img SEGS x -> ~ (hs_partial h1 <= x < hs_partial h1 + APARTIAL)).
{ intros x Hi Hp. refine (blk_img SEGS B LAWS ly1 S1 W m md (hs_partial h1) APARTIAL x HAR H18 _ Hi).
  rewrite RQP. exact Hp. }
(* image bytes are addresses *)
assert (IMR : forall x, in_img SEGS x -> 0 <= x < 2 ^ 64).
{ intros x Hi. pose proof (pa_img_range _ Hi) as Hr. revert Hr. clear. intros. lia. }
(* a G_DR byte outside g_s is kept *)
assert (KI : forall x lo n, inG (G_DR B RG) x -> lo <= x < lo + n ->
  (rg_s RG + 4 * ASRC <= lo \/ lo + n <= rg_s RG) -> abyte_kept W m W m' x).
{ intros x lo n Hg Hx Hd. apply KP; [exact (IMR x (proj1 (HG x Hg))) | | exact (IMP x (proj1 (HG x Hg)))].
  revert Hx Hd HAr. clear. unfold ASRC. intros. lia. }
(* the blocks of the cut: the table and the entry's blocks lie before the partial buffer, the out block after *)
pose proof (df_sep_perm ly1 S1 W m md _ HAR Hperm) as Hpw.
assert (DP : forall q, In q ((dxG cx, ATABLE) :: aentry_blks e1) ->
  zdisjoint (block_rng q) (block_rng (hs_partial h1, APARTIAL))).
{ intros q Hq.
  apply (df_pw_app (fun x y => zdisjoint (block_rng x) (block_rng y)) ((dxG cx, ATABLE) :: aentry_blks e1)
    (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) q (hs_partial h1, APARTIAL) Hpw Hq).
  unfold asrc_blks. cbn [app In]. left. reflexivity. }
assert (Hpw2 : pairwise (fun x y => zdisjoint (block_rng x) (block_rng y))
  (((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1) ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx)).
{ rewrite <- app_comm_cons, <- app_assoc. exact Hpw. }
assert (HGin : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
(* the frame [dsp0 - DRAIN_FRAME, dsp0) is above alloc_ceiling, g_s and the heap below it *)
assert (KS : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W m W m' x).
{ intros x Hx. apply KP.
  - revert Hx Hceil Hslo Hshi H47 ACV. rewrite HDS. clear. unfold DRAIN_FRAME. intros. lia.
  - revert Hx HAr HGhi Hceil Hslo ACV. rewrite HDS. clear. unfold DRAIN_FRAME, ASRC. intros. lia.
  - revert Hx Hpc Hceil Hslo. rewrite RQP, HDS. clear. unfold DRAIN_FRAME. intros. lia. }
(* a byte of a block of the relay entry *)
assert (KB : forall q x, In q (aentry_blks e1) -> fst q <= x < fst q + snd q -> abyte_kept W m W m' x).
{ intros [p n] x Hq Hx. cbn [fst snd] in Hx.
  assert (Hin : In (p, n) (ablocks B ly1 S1)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). right. apply in_or_app. left. exact Hq. }
  destruct (al_blocks SEGS B LAWS ly1 S1 W m md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n (proj1 Hn)) as (_ & Rn).
  apply KP; [exact (df_blk_rng ly1 S1 W m md p n x HAR Hin Hx) | |].
  - intros Hc. apply (df_blk_gs ly1 S1 W m md p n x HAR Hin Hx). revert Hc HAr. clear. unfold ASRC. intros. lia.
  - intros Hc. pose proof (DP (p, n) (or_intror Hq)) as Dq.
    unfold zdisjoint, block_rng in Dq. cbn [fst snd] in Dq. rewrite RQP in Dq.
    revert Hx Hc Dq Rn. clear. intros. lia. }
(* the memory core at m' *)
assert (HMEM' : DMEM B RG cx ly1 S1 W m' md' k1 e1 h2 s1 out1 ev1 (lines (dSTR cx) D) LB1).
{ apply (df_dmem_rebuild cx ly1 S1 W m md k1 e1 h1 s1 out1 ev1 _ LB1 ly1 S1 W m' md' k1 h2 HMEM HJ').
  - (* ROM: image, and not in g_s (HGR) *)
    intros x Hx.
    assert (Hi : in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    assert (N1 : ~ (dHA RG cx + 48 <= x < dHA RG cx + 60)).
    { intros Hc. apply (HGR x); [|exact Hx]. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr.
      cbn [fst snd]. revert Hc HAr. clear. unfold ASRC. intros. lia. }
    rewrite (proj1 (KP x (IMR x Hi) N1 (IMP x Hi))). exact (Hrom x Hx).
  - intros x _ _ _ Hx. exact (Hpres x Hx).
  - reflexivity.
  - exact KS.
  - (* the entry's 56 bytes at SA: in the table block *)
    intros x Hx.
    assert (Hxt : dxG cx <= x < dxG cx + ATABLE) by (revert Hx HGSA HSAG; clear; intros; lia).
    apply KP; [exact (df_blk_rng ly1 S1 W m md (dxG cx) ATABLE x HAR HGin Hxt) | |].
    + intros Hc. apply (df_blk_gs ly1 S1 W m md (dxG cx) ATABLE x HAR HGin).
      * revert Hx HGSA HSAG. clear. intros. lia.
      * revert Hc HAr. clear. unfold ASRC. intros. lia.
    + intros Hc. pose proof (DP (dxG cx, ATABLE) (or_introl eq_refl)) as Dq.
      unfold zdisjoint, block_rng in Dq. cbn [fst snd] in Dq. rewrite RQT, RQP in Dq.
      revert Hx Hc Dq HGSA HSAG. clear. intros. lia.
  - (* the entry's blocks *)
    intros r Hr x Hx. pose proof Hokx as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & _).
    unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    + destruct (Z.eqb_spec (re_cap e1) 0) as [Hc0 | Hc0]; cbn [In] in Hr; [destruct Hr|].
      destruct Hr as [<- | []]. unfold gfp in Hx. cbn [fst snd] in Hx. unfold bzs in Hx.
      rewrite length_map, length_app in Hx.
      destruct Hbuf as [(Hc & _) | (Hc & _ & Hjk & _)]; [exfalso; exact (Hc0 Hc)|].
      apply (KB (re_buf e1, re_cap e1)).
      * unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
      * cbn [fst snd]. revert Hx HU Hjk. clear. intros. lia.
    + cbn [In] in Hr. destruct Hr as [<- | Hr].
      * unfold gfp in Hx. cbn [fst snd] in Hx.
        destruct Hhp as [(Hz & Hke) | (Hz & _ & Hk1 & _ & _)].
        -- exfalso. rewrite Hke in Hx. unfold bzs, key_ptrs in Hx. cbn [map concat length] in Hx.
           revert Hx. clear. intros. lia.
        -- unfold bzs in Hx. rewrite length_map, df_key_ptrs_len in Hx. unfold re_nheld in Hk1.
           apply (KB (re_hp e1, re_kh e1)).
           ++ unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
              rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
           ++ cbn [fst snd]. revert Hx Hk1. clear. intros. lia.
      * apply in_map_iff in Hr as (kk & <- & Hk). unfold gfp in Hx. cbn [fst snd] in Hx.
        unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx.
        apply (KB (key_addr kk, Z.of_nat (length (key_text kk)) + 1)).
        -- unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
           apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
        -- cbn [fst snd]. revert Hx. clear. intros. lia.
  - (* g_s outside slot j: image, outside [HA + 48, HA + 60) *)
    intros x Hx1 Hx2.
    assert (Hgx : inG (G_DR B RG) x)
      by (unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx1).
    apply KP; [exact (IMR x (proj1 (HG x Hgx))) | | exact (IMP x (proj1 (HG x Hgx)))].
    revert Hx2. clear. unfold ASRC. intros. lia.
  - (* the controller's cells and g_out's block *)
    pose proof HRGD as HR. cbn [zpairwise_disjoint zall_disjoint zdisj fst snd] in HR.
    destruct HR as (_ & _ & (_ & Dcb & Dse & _ & _ & Dno & Dca & Dou & Der & _) & _).
    intros r Hr x Hx. unfold aout_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Hx.
    + exact (KC x (or_introl Hx)).
    + apply (KI x (rg_nout RG) 8); [|exact Hx | exact Dno].
      unfold G_DR, G_SL, inG. do 3 apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + apply (KI x (rg_capout RG) 8); [|exact Hx | exact Dca].
      unfold G_DR, G_SL, inG. do 4 apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + apply (KI x (rg_out RG) 8); [|exact Hx | exact Dou].
      unfold G_DR, G_SL, inG. do 5 apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + exact (KC x (or_intror (or_introl Hx))).
    + apply (KI x (rg_client_broken RG) 1); [|exact Hx | exact Dcb].
      unfold G_DR, G_SL, inG. apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + exact (KC x (or_intror (or_intror Hx))).
    + apply (KI x (rg_send_eintr RG) 1); [|exact Hx | exact Dse].
      unfold G_DR, G_SL, inG. do 2 apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + apply (KI x (as_errno B) 4); [|exact Hx | exact Der].
      unfold G_DR, G_SL, inG. do 6 apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + destruct (drain_b_c.ds_ocap s1 =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|].
      destruct Hr as [<- | []]. cbn [fst snd] in Hx.
      assert (Hq : In (out1, drain_b_c.ds_ocap s1) (aout_blks (drain_b_c.ds_ocap s1) out1))
        by (unfold aout_blks; rewrite Hc0; left; reflexivity).
      assert (Hin : In (out1, drain_b_c.ds_ocap s1) (ablocks B ly1 S1)).
      { apply (Permutation_in _ (Permutation_sym Hperm)). right. apply in_or_app. right.
        apply in_or_app. right. apply in_or_app. left. exact Hq. }
      destruct (al_blocks SEGS B LAWS ly1 S1 W m md _ _ HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
      pose proof (req_size_pos _ (proj1 Hn)) as (_ & Rn).
      apply KP; [exact (df_blk_rng ly1 S1 W m md _ _ x HAR Hin Hx) | |].
      * intros Hc. apply (df_blk_gs ly1 S1 W m md _ _ x HAR Hin Hx). revert Hc HAr. clear. unfold ASRC. intros. lia.
      * intros Hc.
        assert (HPin : In (hs_partial h1, APARTIAL) ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1)).
        { right. apply in_or_app. right. unfold asrc_blks. cbn [In]. left. reflexivity. }
        pose proof (df_pw_app (fun x y => zdisjoint (block_rng x) (block_rng y)) _ _
          (hs_partial h1, APARTIAL) (out1, drain_b_c.ds_ocap s1) Hpw2 HPin (in_or_app _ _ _ (or_introl Hq))) as Dq.
        unfold zdisjoint, block_rng in Dq. cbn [fst snd] in Dq. rewrite RQP in Dq.
        revert Hx Hc Dq Rn. clear. intros. lia.
  - exact HS2.
  - assert (EB : asrc_blks h2 = asrc_blks h1) by (unfold asrc_blks; rewrite Epa, Epe, Eex, Ehe; reflexivity).
    rewrite EB. exact Hperm. }
pose proof HMEM' as (_ & _ & _ & _ & HFR' & _).
assert (VK : forall a0 n v0, val_mem SEGS (arm W m) a0 n v0 -> dsp0 cx - DRAIN_FRAME <= a0 ->
  a0 + Z.of_nat n <= dsp0 cx -> val_mem SEGS (arm W m') a0 n v0).
{ intros a0 n v0 Hv H1 H2. apply (akept_vm W m); [|exact Hv]. intros x Hx. apply KS. lia. }
(* the model: the byte pushes no line, so the lines so far and the lines to come are the same *)
pose proof HHIST as (_ & HRef & _).
assert (LS : lines (drain_b_c.ds_ref s1) (firstn (S k) (ddata s1)) =
  lines (drain_b_c.ds_ref s1) (firstn k (ddata s1))).
{ rewrite (df_firstn_nth_app _ _ _ Hb), df_lines_snoc, <- Hstate, Hnone. exact (app_nil_r _). }
assert (LF : lines (dSTR cx) (D ++ firstn (S k) (ddata s1)) = lines (dSTR cx) (D ++ firstn k (ddata s1))).
{ rewrite (df_firstn_nth_app _ _ _ Hb), app_assoc, df_lines_snoc, feed_app, <- HRef, <- Hstate, Hnone.
  exact (app_nil_r _). }
assert (LR : lines (feed (drain_b_c.ds_ref s1) (firstn (S k) (ddata s1))) (skipn (S k) (ddata s1)) =
  lines (feed (drain_b_c.ds_ref s1) (firstn k (ddata s1))) (skipn k (ddata s1))).
{ rewrite (df_skipn_nth _ _ _ Hb), (df_firstn_nth_app _ _ _ Hb), df_feed_snoc, <- Hstate.
  change (b :: skipn (S k) (ddata s1)) with ([b] ++ skipn (S k) (ddata s1)).
  rewrite lines_app, df_lines_one, df_feed_one, Hnone. reflexivity. }
exists out1, ev1, LB1, spent, jb, a, v, rs, tl, r0, rs0.
split.
{ unfold df_slots. split; [exact HFR'|].
  split; [apply (VK _ _ _ M56); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M64); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M48); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M200); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M32); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M24); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M72); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M80); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M40); unfold DRAIN_FRAME; clear; lia|].
  apply (VK _ _ _ M192); unfold DRAIN_FRAME; clear; lia. }
split; [rewrite Epe; exact Hpend|].
split; [exact Hp0|]. split; [exact Hn0|]. split; [exact Hdata|]. split; [exact HMEM'|].
split; [exact HnoNUL|]. split; [exact Hused|].
split; [unfold DSAME in HSAME |- *; rewrite Efd, Eop, Ecl, Epe, Epa, Ehe; exact HSAME|].
split; [exact Hcap|]. split; [exact Hu|]. split; [exact Hskip|]. split; [exact Hkeys|]. split; [exact Hka|].
split; [rewrite Eei; exact Heintr|].
split; [rewrite Epe; exact Hpendm|].
split; [rewrite Eoff; exact Hoff|].
split; [rewrite Hst, (df_firstn_nth_app _ _ _ Hb), df_feed_snoc, <- Hstate; reflexivity|].
split; [rewrite Eex, LS; exact Hen|].
split; [rewrite Eex, LS; exact Hecap|].
split; [unfold DHIST in HHIST |- *; rewrite Eex, LF; exact HHIST|].
split; [exact HRS|].
split; [unfold dpfut in HPFUT |- *; cbv zeta in HPFUT |- *; rewrite LR, LS; exact HPFUT|].
exact HBUD.
Qed.

(* ---- helpers of df_close_push (prefix df_pu_). ---- *)

(* HRGD's pairs, by position (W_drain_epi.v dend_zall / dend_zpw) *)
Lemma df_pu_zall : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma df_pu_zpw : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply df_pu_zall; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Ltac df_pu_zd i j H :=
  pose proof (df_pu_zpw _ i j (0, 0) HRGD ltac:(lia) ltac:(cbn [length]; lia)) as H;
  cbn [nth] in H; unfold zdisj in H; cbn [fst snd] in H.

(* a byte of g_s is in G_DR and is not errno *)
Lemma df_pu_gs : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC ->
inG (G_DR B RG) a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. df_pu_zd 2%nat 11%nat D. split; [|clear - D Ha; lia].
unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha.
Qed.

(* the five cells of G_SL that the call keeps by the image clause: in G_DR, not errno, not g_s *)
Lemma df_pu_sl : forall a,
(rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
 rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8) ->
inG (G_DR B RG) a /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ (rg_s RG <= a < rg_s RG + 4 * ASRC).
Proof.
intros a Ha. unfold G_DR, G_SL, inG.
destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
- df_pu_zd 2%nat 4%nat D1. df_pu_zd 4%nat 11%nat D2.
  split; [apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Ha|].
  clear - D1 D2 Ha. split; lia.
- df_pu_zd 2%nat 5%nat D1. df_pu_zd 5%nat 11%nat D2.
  split; [do 2 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Ha|].
  clear - D1 D2 Ha. split; lia.
- df_pu_zd 2%nat 8%nat D1. df_pu_zd 8%nat 11%nat D2.
  split; [do 3 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Ha|].
  clear - D1 D2 Ha. split; lia.
- df_pu_zd 2%nat 9%nat D1. df_pu_zd 9%nat 11%nat D2.
  split; [do 4 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Ha|].
  clear - D1 D2 Ha. split; lia.
- df_pu_zd 2%nat 10%nat D1. df_pu_zd 10%nat 11%nat D2.
  split; [do 5 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Ha|].
  clear - D1 D2 Ha. split; lia.
Qed.

(* writability across a change of world: the new world does not hide the byte and its presence is kept *)
Lemma df_pu_wr : forall (H H' : word -> bool) (m m' : word -> option byte) a,
H' (Z_to_bv 64 a) = false -> (apresent H m a -> apresent H' m' a) ->
writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H' m') a.
Proof.
intros H H' m m' a EH' Hp Hw. unfold writable_at, wview, mrestrict in *. rewrite EH'. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
  + destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* two blocks at different positions of a permutation of the live blocks start at different addresses *)
Lemma df_pu_ne : forall ly S (W : world SEGS) m md (x y : Z * Z) l,
AR SEGS B ly S W m md -> Permutation (ablocks B ly S) (x :: y :: l) -> fst x <> fst y.
Proof.
intros ly S W m md x y l HAR HP Heq.
pose proof (sep_blocks_perm SEGS B LAWS ly S W m md x y l HAR HP) as Hd.
assert (Hx : In x (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (Hy : In y (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; left; reflexivity).
destruct x as [px nx], y as [py ny].
destruct (al_blocks SEGS B LAWS ly S W m md px nx HAR Hx) as (_ & _ & _ & _ & _ & _ & Hnx).
destruct (al_blocks SEGS B LAWS ly S W m md py ny HAR Hy) as (_ & _ & _ & _ & _ & _ & Hny).
pose proof (req_size_pos nx (proj1 Hnx)) as (Rx & _). pose proof (req_size_pos ny (proj1 Hny)) as (Ry & _).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd, Heq. clear - Hd Heq Rx Ry. lia.
Qed.

Lemma df_pu_ne_in : forall ly S (W : world SEGS) m md (x y : Z * Z) L,
AR SEGS B ly S W m md -> Permutation (ablocks B ly S) (x :: L) -> In y L -> fst x <> fst y.
Proof.
intros ly S W m md x y L HAR HP Hy.
destruct (in_split _ _ Hy) as (l1 & l2 & ->).
apply (df_pu_ne ly S W m md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

(* the addresses of a stretch of a permutation of the live blocks are distinct *)
Lemma df_pu_nd : forall ly S (W : world SEGS) m md L2 L1 L3,
AR SEGS B ly S W m md -> Permutation (ablocks B ly S) (L1 ++ L2 ++ L3) -> List.NoDup (map fst L2).
Proof.
intros ly S W m md L2. induction L2 as [|x L2 IH]; intros L1 L3 HAR HP; [apply List.NoDup_nil|].
cbn [map]. apply List.NoDup_cons.
- intros Hin. apply in_map_iff in Hin as (y & Hy & Hin).
  assert (HP2 : Permutation (ablocks B ly S) (x :: L1 ++ L2 ++ L3)).
  { eapply Permutation_trans; [exact HP|]. cbn [app]. apply Permutation_sym, Permutation_middle. }
  exact (df_pu_ne_in ly S W m md x y (L1 ++ L2 ++ L3) HAR HP2
    ltac:(apply in_or_app; right; apply in_or_app; left; exact Hin) (eq_sym Hy)).
- apply (IH (L1 ++ [x]) L3 HAR). rewrite <- app_assoc. exact HP.
Qed.

Lemma df_pu_lb : forall l, map fst (alist_blks l) = list_blocks l.
Proof.
intros l. unfold alist_blks, list_blocks. rewrite map_app, map_map. cbn [fst].
destruct (hl_cap l =? 0); reflexivity.
Qed.

Lemma df_pu_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma df_pu_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

(* a list's footprint is kept when its 16 bytes and the bytes of its blocks are *)
Lemma df_pu_alist_kept : forall ly S (W W' : world SEGS) m m' LA l lines,
alist_at B ly S W m LA l lines ->
(forall a, LA <= a < LA + 16 -> abyte_kept W m W' m' a) ->
(forall p n a, In (p, n) (alist_blks l) -> p <= a < p + req_size n -> abyte_kept W m W' m' a) ->
akept W m W' m' (alist_fp LA l).
Proof.
intros ly S W W' m m' LA l lines HL KLA KB r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & _).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. exact (KLA a Ha).
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + revert Hr. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; intros Hr; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, df_pu_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [clear - Hc Hc0; lia|].
    apply (KB (hl_v l) (AREC * hl_cap l)).
    * unfold alist_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc0). apply in_or_app. left. left. reflexivity.
    * pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; clear - Hc; lia)) as (_ & Hrq).
      clear - Ha Hj Hrq Hn. unfold hl_n, AREC in *. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (KB (fst q) (Z.of_nat (length (snd q)) + 1)).
    * unfold alist_blks. apply in_or_app. right.
      apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
    * pose proof (req_size_pos (Z.of_nat (length (snd q)) + 1) ltac:(lia)) as (_ & Hrq). clear - Ha Hrq. lia.
Qed.

(* the relay entry's footprint is kept when the bytes of its blocks are *)
Lemma df_pu_aentry_kept : forall ly S (W W' : world SEGS) m m' e,
aentry_okx B ly S W m e ->
(forall p n a, In (p, n) (aentry_blks e) -> p <= a < p + req_size n -> abyte_kept W m W' m' a) ->
akept W m W' m' (aentry_fp e).
Proof.
intros ly S W W' m m' e HE KB r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & _).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- revert Hr. destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; intros Hr; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [clear - Hc Hc0; lia|].
  apply (KB (re_buf e) (re_cap e)).
  + unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + pose proof (req_size_pos (re_cap e) ltac:(clear - Hc; lia)) as (_ & Hrq). clear - Ha HU Hj Hrq. lia.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. clear - Ha. lia.
    * unfold bzs in Ha. rewrite length_map, df_pu_key_ptrs_len in Ha. unfold re_nheld in Hk1.
      apply (KB (re_hp e) (re_kh e)).
      -- unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
         rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
      -- pose proof (req_size_pos (re_kh e) ltac:(clear - Hk2; lia)) as (_ & Hrq). clear - Ha Hk1 Hrq. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (KB (key_addr k) (Z.of_nat (length (key_text k)) + 1)).
    * unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
    * pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). clear - Ha Hrq. lia.
Qed.

(* the model's capacity after one more push (plain drain_b.v pcapm_app, its one-line case) *)
Lemma df_pu_pcapm_cons : forall n c l ls, pcapm n c (l :: ls) = pcapm (n + 1) (drain_b_c.push_cap n c) ls.
Proof. intros n c l ls. unfold pcapm at 1. cbn [drain_b_c.pushes_run fst snd]. apply pushes_run_m. Qed.

Lemma df_pu_pcapm_snoc : forall ls n c w,
pcapm n c (ls ++ [w]) = drain_b_c.push_cap (n + Z.of_nat (length ls)) (pcapm n c ls).
Proof.
induction ls as [|l ls IH]; intros n c w.
- cbn [app length Z.of_nat]. rewrite ?Z.add_0_r, df_pu_pcapm_cons. reflexivity.
- rewrite <- app_comm_cons, !df_pu_pcapm_cons, IH.
  replace (n + 1 + Z.of_nat (length ls)) with (n + Z.of_nat (length (l :: ls))) by (cbn [length]; lia).
  reflexivity.
Qed.

Lemma df_pu_len_snoc : forall {A} (l : list A) (x : A) z, z + Z.of_nat (length (l ++ [x])) = z + Z.of_nat (length l) + 1.
Proof. intros A l x z. rewrite length_app. cbn [length]. lia. Qed.

Lemma df_pu_grow_push : forall n c, ListRep.grow_cap n c = drain_b_c.push_cap n c.
Proof. intros n c. unfold ListRep.grow_cap, drain_b_c.push_cap. destruct (n =? c), (c =? 0); lia. Qed.

Lemma df_pu_bzs_inv : forall l, map (Z_to_bv 8) (bzs l) = l.
Proof.
intros l. unfold bzs. rewrite map_map. induction l as [|x l IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
apply bv_eq. unfold bz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma df_pu_skipn_cons : forall {A} (l : list A) n x, nth_error l n = Some x -> skipn n l = x :: skipn (S n) l.
Proof.
intros A l. induction l as [|y l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
destruct n as [|n]; cbn in Hn |- *; [injection Hn as ->; reflexivity | apply IH; exact Hn].
Qed.

(* the meter over a trace's parts (W_drain_gs.v:738-761) *)
Lemma df_pu_tr_cost_app : forall (t1 t2 : dtrace), tr_cost MT (t1 ++ t2) = tr_cost MT t1 + tr_cost MT t2.
Proof.
intros t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

Lemma df_pu_tr_alloc_app : forall (t1 t2 : dtrace), tr_alloc (t1 ++ t2) = tr_alloc t1 + tr_alloc t2.
Proof.
intros t1 t2. unfold tr_alloc. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

Lemma df_pu_tr_max_nonneg : forall (t : dtrace), 0 <= tr_max t.
Proof.
intros t. unfold tr_max. induction t as [|ev t IH]; [cbn [fold_right]; lia|].
cbn [fold_right]. destruct ev; lia.
Qed.

Lemma df_pu_tr_max_app : forall (t1 t2 : dtrace), tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof.
intros t1 t2. pose proof (df_pu_tr_max_nonneg t2) as H2. unfold tr_max in *.
induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

(* list_push's charge is its requests' cost less one free; its requests' bytes *)
Lemma df_pu_lp_cost : forall (l : hlist) (v : dadrF) n,
lp_cost MT l n + mo_free MT = tr_cost MT (ListTr.list_push_tra v (hl_n l) (hl_cap l) n).
Proof.
intros l v n. unfold lp_cost, lp_grow, lp_vbytes, ListTr.list_push_tra, tr_cost, ListRep.grow_cap.
destruct (hl_n l =? hl_cap l); [destruct (hl_cap l =? 0)|]; cbn [app fold_right].
- replace (AREC * 8) with 128 by (unfold AREC; lia). lia.
- replace (AREC * (2 * hl_cap l)) with (32 * hl_cap l) by (unfold AREC; lia). lia.
- lia.
Qed.

Lemma df_pu_lp_alloc : forall (v : dadrF) N C n,
tr_alloc (ListTr.list_push_tra v N C n) = (if N =? C then (if C =? 0 then 128 else 32 * C) else 0) + (n + 1).
Proof.
intros v N C n. unfold tr_alloc, ListTr.list_push_tra.
destruct (N =? C); [destruct (C =? 0)|]; cbn [app fold_right]; lia.
Qed.

(* the budget after the push: spent grows by list_push's charge, the trace loses the push's requests *)
Lemma df_pu_bud : forall cx S1 S2 spent (l : hlist) (v : dadrF) N C n n' tl' bb,
dbud MT MMAX cx S1 spent (ListTr.list_push_tra v N C n ++ tl') ->
hl_n l = N -> hl_cap l = C -> n = n' -> 0 <= n' -> 0 <= C ->
mo_le MT S1 S2 (lp_cost MT l n') ->
blocks_bytes S1 = bb + AREC * hl_cap l ->
blocks_bytes S2 = bb + AREC * ListRep.grow_cap (hl_n l) (hl_cap l) + (n' + 1) ->
dbud MT MMAX cx S2 (spent + lp_cost MT l n') tl'.
Proof.
intros cx S1 S2 spent l v N C n n' tl' bb (B1 & B2 & B3 & B4 & B5) EN EC En Hn HC Hmle E1 E2.
subst N C n.
pose proof (df_pu_lp_cost l v n') as EL.
pose proof (mo_free_nonneg MT MTL) as F0.
pose proof (mo_malloc_nonneg MT MTL (n' + 1) ltac:(lia)) as M1.
pose proof (mo_malloc_nonneg MT MTL (lp_vbytes l)
  ltac:(clear - HC; unfold lp_vbytes, AREC, ListRep.grow_cap;
        destruct (hl_n l =? hl_cap l), (hl_cap l =? 0); lia)) as M2.
rewrite df_pu_tr_cost_app in B3. rewrite df_pu_tr_max_app in B5.
split; [exact (mo_le_trans MT MTL _ _ _ _ _ B1 Hmle)|].
split; [clear - B2 F0 M1 M2; unfold lp_cost; destruct (lp_grow l); lia|].
split; [clear - B3 EL F0; lia|].
split; [|clear - B5; lia].
(* C3: list_push's requests move the live bytes by exactly their net change (the vector's growth, new before old,
   then strndup's n' + 1 bytes), so the peak of the rest stays in room (W_tr_peak.v tr_peak_app) *)
assert (EN : tr_net (ListTr.list_push_tra v (hl_n l) (hl_cap l) n') =
  (if hl_n l =? hl_cap l then (if hl_cap l =? 0 then 128 else 16 * hl_cap l) else 0) + (n' + 1)).
{ unfold tr_net, ListTr.list_push_tra.
  destruct (hl_n l =? hl_cap l); [destruct (hl_cap l =? 0)|]; cbn [app fold_right]; lia. }
rewrite (W_tr_peak.tr_peak_app _ tl'), EN, E1 in B4. rewrite E2. clear - B4 HC. unfold ListRep.grow_cap, AREC in *.
destruct (Z.eqb_spec (hl_n l) (hl_cap l)); [destruct (Z.eqb_spec (hl_cap l) 0)|]; cbv iota in *; lia.
Qed.

Lemma df_pu_swap : forall {A} (l1 l2 l3 : list A), Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof. intros A l1 l2 l3. rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm. Qed.

Lemma df_pu_mid : forall {A} (a : A) l1 l2 l3 l4, Permutation (a :: l1 ++ l2 ++ l3 ++ l4) ((l1 ++ l2 ++ l3) ++ a :: l4).
Proof.
intros A a l1 l2 l3 l4. pose proof (Permutation_middle (l1 ++ l2 ++ l3) l4 a) as H.
rewrite <- !app_assoc in H. rewrite <- !app_assoc. exact H.
Qed.

(* the cut's block list with the expected list's vector moved to the front *)
Lemma df_pu_perm_old : forall (GA PA : Z * Z) AE P OV RECS Hd AO R,
Permutation (GA :: AE ++ (PA :: P ++ (OV ++ RECS) ++ Hd) ++ AO ++ R)
  (OV ++ GA :: AE ++ (PA :: P ++ RECS ++ Hd) ++ AO ++ R).
Proof.
intros.
assert (E1 : GA :: AE ++ (PA :: P ++ (OV ++ RECS) ++ Hd) ++ AO ++ R =
  (GA :: AE ++ PA :: P) ++ OV ++ (RECS ++ Hd ++ AO ++ R))
  by (cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity).
assert (E2 : GA :: AE ++ (PA :: P ++ RECS ++ Hd) ++ AO ++ R = (GA :: AE ++ PA :: P) ++ (RECS ++ Hd ++ AO ++ R))
  by (cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity).
rewrite E1, E2. apply df_pu_swap.
Qed.

(* the new text's block D and the new vector OV2 put in their places in the cut's block list *)
Lemma df_pu_perm_new : forall (GA PA D : Z * Z) AE P OV2 RECS Hd AO R,
Permutation (D :: OV2 ++ GA :: AE ++ (PA :: P ++ RECS ++ Hd) ++ AO ++ R)
  (GA :: AE ++ (PA :: P ++ (OV2 ++ RECS ++ [D]) ++ Hd) ++ AO ++ R).
Proof.
intros.
assert (E1 : GA :: AE ++ (PA :: P ++ RECS ++ Hd) ++ AO ++ R = (GA :: AE ++ PA :: P) ++ (RECS ++ Hd ++ AO ++ R))
  by (cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity).
assert (E2 : GA :: AE ++ (PA :: P ++ (OV2 ++ RECS ++ [D]) ++ Hd) ++ AO ++ R =
  ((GA :: AE ++ PA :: P) ++ OV2 ++ RECS) ++ D :: (Hd ++ AO ++ R))
  by (cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity).
rewrite E1, E2.
eapply Permutation_trans; [apply perm_skip; apply df_pu_swap|]. apply df_pu_mid.
Qed.

Ltac df_pu_in := first [ assumption | solve [left; reflexivity] | solve [apply in_or_app; left; df_pu_in]
  | solve [apply in_or_app; right; df_pu_in] | solve [right; df_pu_in] ].

(* the NUL byte with h->overlong = 0: list_push (h->expected, h->partial, h->npartial) at 0x834f0, then
   h->npartial = 0 and h->overlong = 0.  l2 is the list list_push leaves (lp_post), d its new text's block;
   the state is the one the two stores leave at 0x83544. *)
Lemma df_close_push : forall cx s1 D k p0 ly1 S1 k1 W m md e1 h1 ly2 S2 k2 W2 m2 md2 l2 d,
DBASE B MT MMAX RG cx ->
df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 ->
nth_error (ddata s1) k = Some 0 -> hs_overlong h1 = 0 ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 W2 m2 md2 k2 ->
(forall p n i, In (p, n) (ablocks B ly1 S1) -> p <> hl_v (hs_expected h1) -> 0 <= i < req_size n ->
   abyte_kept W m W2 m2 (p + i)) ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) -> ~ (dHA RG cx + 64 <= a < dHA RG cx + 80) ->
   abyte_kept W m W2 m2 a) ->
(forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_client RG <= a < rg_client RG + 4) \/
   (rg_send_dead RG <= a < rg_send_dead RG + 1) \/ (as_errno B <= a < as_errno B + 4) ->
   abyte_kept W m W2 m2 a) ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W2 m2 a) ->
rom_view SEGS W2 m2 -> apres_kept B W m W2 m2 -> frames S2 = frames S1 ->
alist_at B ly2 S2 W2 m2 (dHA RG cx + 64) l2 true ->
val_mem SEGS (arm W2 m2) (dHA RG cx + 48) 8 0 -> val_mem SEGS (arm W2 m2) (dHA RG cx + 56) 4 0 ->
hl_recs l2 = hl_recs (hs_expected h1) ++ [(d, hs_W h1)] ->
hl_cap l2 = ListRep.grow_cap (hl_n (hs_expected h1)) (hl_cap (hs_expected h1)) ->
(lp_grow (hs_expected h1) = false -> hl_v l2 = hl_v (hs_expected h1)) ->
(forall rest,
 Permutation (ablocks B ly1 S1)
   ((if lp_grow (hs_expected h1) && negb (hl_cap (hs_expected h1) =? 0)
     then [(hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))] else []) ++ rest) ->
 Permutation (ablocks B ly2 S2)
   ((d, Z.of_nat (length (hs_W h1)) + 1) ::
    (if lp_grow (hs_expected h1) then [(hl_v l2, AREC * hl_cap l2)] else []) ++ rest)) ->
mo_le MT S1 S2 (lp_cost MT (hs_expected h1) (Z.of_nat (length (hs_W h1)))) ->
df_cutjh cx s1 D (S k) p0 ly2 S2 k2 W2 m2 md2 e1
  (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
      (hs_pjunk h1) 0 0 (hs_pad h1) l2 (hs_held h1)).
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md e1 h1 ly2 S2 k2 W2 m2 md2 l2 d HB HC Hnth Hov HJ2 Hbk Hik Hcell Hfr
  Hrom2 Hpres2 Hfrm2 Hl2 Hnp2 Hov2 Hrecs2 Hcap2 Hv2 HLP Hmle2.
match goal with |- df_cutjh _ _ _ _ _ _ _ _ _ _ _ _ ?H => set (h2 := H) end.
destruct HC as (out1 & ev1 & LB1 & spent & jb & ad & v0 & rs & tl & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) &
  Hpend & Hp0 & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
pose proof HMEM as (HJ & Hrom & Hpres & Hfrs & HFRd & Hent & Hawr & Hokx & Hsrc & Hoth & Hgsk & Hout & Hlive & Hperm).
pose proof Hsrc as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & H24).
destruct HB as (_ & _ & _ & HSAlo & HSAhi & _ & _ & _ & Hj & _).
assert (HAR1 : AR SEGS B ly1 S1 W m md) by (eapply ajournal_gx_AR; exact HJ).
assert (HAR2 : AR SEGS B ly2 S2 W2 m2 md2) by (eapply ajournal_gx_AR; exact HJ2).
assert (HHA : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC)
  by (revert Hj; clear; intros Hj; unfold dHA, ASRC; lia).
pose proof H22 as (_ & _ & _ & _ & Hncap & Hvdisj & _).
assert (HC0 : 0 <= hl_cap (hs_expected h1)) by (clear - Hncap; unfold hl_n in Hncap; lia).
(* ---- the blocks: the cut's list with the expected list's vector OV in front of the rest R0 ---- *)
pose (RECS := map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs (hs_expected h1))).
pose (OV := if hl_cap (hs_expected h1) =? 0 then []
  else [(hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))]).
pose (OV2 := if hl_cap l2 =? 0 then [] else [(hl_v l2, AREC * hl_cap l2)]).
pose (R0 := (dxG cx, ATABLE) :: aentry_blks e1 ++ ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ RECS ++
  alist_blks (hs_held h1)) ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx).
assert (P0 : Permutation (ablocks B ly1 S1) (OV ++ R0)).
{ change (asrc_blks h1) with ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ (OV ++ RECS) ++
    alist_blks (hs_held h1)) in Hperm.
  eapply Permutation_trans; [exact Hperm|]. unfold R0. apply df_pu_perm_old. }
assert (IN0 : forall b, In b R0 -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym P0)); apply in_or_app; right; exact Hb).
assert (NV : forall p n, In (p, n) R0 -> p <> hl_v (hs_expected h1)).
{ intros p n Hin. destruct Hvdisj as [(Hc0 & Hv0) | (Hcp & _)].
  - rewrite Hv0. destruct (al_blocks SEGS B LAWS ly1 S1 W m md p n HAR1 (IN0 _ Hin)) as (_ & H4096 & _).
    clear - H4096. lia.
  - assert (P0' : Permutation (ablocks B ly1 S1)
      ((hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1)) :: R0)).
    { unfold OV in P0. rewrite (proj2 (Z.eqb_neq (hl_cap (hs_expected h1)) 0) ltac:(clear - Hcp; lia)) in P0.
      exact P0. }
    intros Heq. exact (df_pu_ne_in ly1 S1 W m md _ (p, n) R0 HAR1 P0' Hin (eq_sym Heq)). }
assert (KB : forall p n x, In (p, n) R0 -> p <= x < p + req_size n -> abyte_kept W m W2 m2 x).
{ intros p n x Hin Hx.
  pose proof (Hbk p n (x - p) (IN0 _ Hin) (NV p n Hin) ltac:(clear - Hx; lia)) as Hk.
  replace (p + (x - p)) with x in Hk by ring. exact Hk. }
(* ---- the image bytes the call keeps ---- *)
assert (IKs : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx + 48 <= x < dHA RG cx + 60) ->
  ~ (dHA RG cx + 64 <= x < dHA RG cx + 80) -> abyte_kept W m W2 m2 x).
{ intros x Hx Q1 Q2. destruct (df_pu_gs x Hx) as (HinG & Hne). destruct (HG x HinG) as (Him & Hno & _).
  exact (Hik x Him Hno Hne Q1 Q2). }
assert (IKj : forall x, dHA RG cx <= x < dHA RG cx + ASRC -> ~ (dHA RG cx + 48 <= x < dHA RG cx + 60) ->
  ~ (dHA RG cx + 64 <= x < dHA RG cx + 80) -> abyte_kept W m W2 m2 x).
{ intros x Hx Q1 Q2. apply IKs; [clear - Hx HHA; lia | exact Q1 | exact Q2]. }
assert (IKo : forall x, (rg_client_broken RG <= x < rg_client_broken RG + 1 \/
  rg_send_eintr RG <= x < rg_send_eintr RG + 1 \/ rg_nout RG <= x < rg_nout RG + 8 \/
  rg_capout RG <= x < rg_capout RG + 8 \/ rg_out RG <= x < rg_out RG + 8) -> abyte_kept W m W2 m2 x).
{ intros x Hx. destruct (df_pu_sl x Hx) as (HinG & Hne & Hngs). destruct (HG x HinG) as (Him & Hno & _).
  apply (Hik x Him Hno Hne); intros Hc; apply Hngs; destruct HHA as [Q1 Q2]; unfold ASRC in Q1, Q2 |- *;
  clear - Hc Q1 Q2; lia. }
(* h->npartial and h->overlong: written by the two stores, writable because present and not hidden *)
assert (WR : forall x, dHA RG cx + 48 <= x < dHA RG cx + 60 -> writable_at SEGS (arm W2 m2) x).
{ intros x Hx.
  assert (Hxs : rg_s RG <= x < rg_s RG + 4 * ASRC)
    by (destruct HHA as [Q1 Q2]; unfold ASRC in Q1, Q2 |- *; clear - Hx Q1 Q2; lia).
  destruct (df_pu_gs x Hxs) as (HinG & Hne). destruct (HG x HinG) as (Him & Hno & _).
  unfold arm. apply (df_pu_wr (w_H W) (w_H W2) m m2 x).
  - apply (hidden_not_img SEGS). rewrite unsigned_lit_small by (pose proof HGSB as HGB; clear - Hxs HGB; lia).
    exact Him.
  - exact (Hpres2 x Him Hno Hne).
  - pose proof (H5 (x - dHA RG cx) ltac:(clear - Hx; unfold ASRC; lia)) as Hw.
    replace (dHA RG cx + (x - dHA RG cx)) with x in Hw by ring. exact Hw. }
(* ---- the blocks after the push ---- *)
assert (NP0 : Permutation (ablocks B ly2 S2) ((d, Z.of_nat (length (hs_W h1)) + 1) :: OV2 ++ R0)).
{ destruct (lp_grow (hs_expected h1)) eqn:EG; rewrite ?EG in HLP.
  - assert (Hnz : hl_cap l2 <> 0).
    { rewrite Hcap2. unfold lp_grow in EG. apply Z.eqb_eq in EG. unfold ListRep.grow_cap. rewrite EG, Z.eqb_refl.
      clear - HC0. destruct (Z.eqb_spec (hl_cap (hs_expected h1)) 0); cbv iota; lia. }
    assert (Hpre : Permutation (ablocks B ly1 S1) ((if true && negb (hl_cap (hs_expected h1) =? 0)
      then [(hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))] else []) ++ R0)).
    { revert P0. unfold OV. destruct (hl_cap (hs_expected h1) =? 0); intros P0; exact P0. }
    pose proof (HLP R0 Hpre) as HQ. unfold OV2. rewrite (proj2 (Z.eqb_neq (hl_cap l2) 0) Hnz). exact HQ.
  - assert (Hpre : Permutation (ablocks B ly1 S1) ((if false && negb (hl_cap (hs_expected h1) =? 0)
      then [(hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))] else []) ++ (OV ++ R0))) by exact P0.
    pose proof (HLP (OV ++ R0) Hpre) as HQ.
    assert (EOV : OV2 = OV).
    { unfold OV2, OV. rewrite Hcap2, (Hv2 eq_refl). unfold lp_grow in EG. unfold ListRep.grow_cap. rewrite EG.
      reflexivity. }
    rewrite EOV. exact HQ. }
assert (NP : Permutation (ablocks B ly2 S2)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h2 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx)).
{ eapply Permutation_trans; [exact NP0|].
  change (asrc_blks h2) with ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ alist_blks l2 ++
    alist_blks (hs_held h1)).
  assert (EL2 : alist_blks l2 = OV2 ++ RECS ++ [(d, Z.of_nat (length (hs_W h1)) + 1)])
    by (unfold alist_blks; rewrite Hrecs2, map_app; reflexivity).
  rewrite EL2. unfold R0. apply df_pu_perm_new. }
assert (IN2 : forall b, In b ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ alist_blks l2 ++
  alist_blks (hs_held h1)) -> In b (ablocks B ly2 S2)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym NP)). right. apply in_or_app. right. apply in_or_app. left.
  exact Hb. }
(* ---- the harness source after the push ---- *)
assert (HS2 : asrc_at B ly2 S2 W2 m2 (dHA RG cx) h2).
{ unfold asrc_at, h2.
  cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
    hs_expected hs_held].
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H1]|].
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H2]|].
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H3]|].
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H4]|].
  split.
  { intros i Hi.
    assert (Hcase : (48 <= i < 60) \/ (64 <= i < 80) \/ (~ (48 <= i < 60) /\ ~ (64 <= i < 80))) by (clear; lia).
    destruct Hcase as [Q|[Q|[Q1 Q2]]].
    - apply WR. clear - Q. lia.
    - pose proof Hl2 as (_ & _ & _ & Hl2w & _). pose proof (Hl2w (i - 64) ltac:(clear - Q; lia)) as Hw.
      replace (dHA RG cx + 64 + (i - 64)) with (dHA RG cx + i) in Hw by ring. exact Hw.
    - apply (proj2 (IKj (dHA RG cx + i) ltac:(clear - Hi; lia) ltac:(clear - Q1; lia) ltac:(clear - Q2; lia))).
      exact (H5 i Hi). }
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split.
  { apply (alist_at_kept B ly1 S1 W m ly2 S2 W2 m2 (dHA RG cx + 16) (hs_pending h1) false H10).
    - apply (df_pu_alist_kept ly1 S1 W W2 m m2 (dHA RG cx + 16) (hs_pending h1) false H10).
      + intros x Hx. apply IKj; clear - Hx; unfold ASRC; lia.
      + intros p n x Hin Hx. apply (KB p n x); [unfold R0; df_pu_in | exact Hx].
    - intros b Hb. apply IN2. right. apply in_or_app. left. exact Hb. }
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H11]|].
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H12]|].
  split; [exact Hnp2|]. split; [exact Hov2|]. split; [exact H15|].
  split; [clear; unfold APARTIAL; lia|]. split; [left; reflexivity|].
  split; [apply IN2; left; reflexivity|]. split; [exact H19|].
  split.
  { apply (akept_garr8 W m); [|exact H20]. intros x Hx.
    apply (KB (hs_partial h1) APARTIAL x); [unfold R0; df_pu_in|].
    unfold bzs in Hx. rewrite length_map, H19 in Hx. change (req_size APARTIAL) with 6000.
    clear - Hx. unfold APARTIAL in *. lia. }
  split; [intros Hc; exact Hc|].
  split; [exact Hl2|].
  split.
  { apply (alist_at_kept B ly1 S1 W m ly2 S2 W2 m2 (dHA RG cx + 80) (hs_held h1) true H23).
    - apply (df_pu_alist_kept ly1 S1 W W2 m m2 (dHA RG cx + 80) (hs_held h1) true H23).
      + intros x Hx. apply IKj; clear - Hx; unfold ASRC; lia.
      + intros p n x Hin Hx. apply (KB p n x); [unfold R0; df_pu_in | exact Hx].
    - intros b Hb. apply IN2. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  assert (ND : List.NoDup (map fst ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ alist_blks l2 ++
    alist_blks (hs_held h1)))).
  { apply (df_pu_nd ly2 S2 W2 m2 md2 _ ((dxG cx, ATABLE) :: aentry_blks e1)
      (aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) HAR2). exact NP. }
  cbn [map fst] in ND. rewrite !map_app, !df_pu_lb in ND.
  unfold hs_blocks. cbn [hs_pending hs_partial hs_expected hs_held].
  apply NoDup_ListNoDup. exact (Permutation_NoDup (Permutation_middle _ _ _) ND). }
(* ---- DMEM after the push ---- *)
assert (KA : forall x, dxSA cx <= x < dxSA cx + AENT -> abyte_kept W m W2 m2 x).
{ intros x Hx. apply (KB (dxG cx) ATABLE x); [unfold R0; left; reflexivity|].
  change (req_size ATABLE) with 896. clear - Hx HSAlo HSAhi. unfold AENT, ATABLE in *. lia. }
assert (KE : akept W m W2 m2 (aentry_fp e1)).
{ apply (df_pu_aentry_kept ly1 S1 W W2 m m2 e1 Hokx). intros p n x Hin Hx.
  apply (KB p n x); [unfold R0; df_pu_in | exact Hx]. }
assert (KG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
  abyte_kept W m W2 m2 x).
{ intros x Hx1 Hx2. apply IKs; [exact Hx1 | intros Hc; apply Hx2; clear - Hc; unfold ASRC; lia
  | intros Hc; apply Hx2; clear - Hc; unfold ASRC; lia]. }
assert (KO : akept W m W2 m2 (aout_fp B RG (drain_b_c.ds_ocap s1) out1)).
{ intros r Hr x Hx. unfold aout_fp in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd] in Hx.
  - apply Hcell. left. exact Hx.
  - apply IKo. right; right; left. exact Hx.
  - apply IKo. right; right; right; left. exact Hx.
  - apply IKo. right; right; right; right. exact Hx.
  - apply Hcell. right; left. exact Hx.
  - apply IKo. left. exact Hx.
  - apply Hcell. right; right; left. exact Hx.
  - apply IKo. right; left. exact Hx.
  - apply Hcell. right; right; right. exact Hx.
  - revert Hr. destruct (Z.eqb_spec (drain_b_c.ds_ocap s1) 0) as [E0|E0]; intros Hr; [destruct Hr|].
    destruct Hr as [<-|[]]. cbn [fst snd] in Hx.
    assert (Hin : In (out1, drain_b_c.ds_ocap s1) R0).
    { unfold R0, aout_blks. rewrite (proj2 (Z.eqb_neq _ _) E0). df_pu_in. }
    destruct (al_blocks SEGS B LAWS ly1 S1 W m md _ _ HAR1 (IN0 _ Hin)) as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (req_size_pos (drain_b_c.ds_ocap s1) (proj1 Hn)) as (_ & Hrq).
    apply (KB _ _ x Hin). clear - Hx Hrq. lia. }
assert (HMEM2 : DMEM B RG cx ly2 S2 W2 m2 md2 k2 e1 h2 s1 out1 ev1 (lines (dSTR cx) D) LB1)
  by exact (df_dmem_rebuild cx ly1 S1 W m md k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ly2 S2 W2 m2 md2 k2 h2
    HMEM HJ2 Hrom2 Hpres2 Hfrm2 Hfr KA KE KG KO HS2 NP).
pose proof HMEM2 as (_ & _ & _ & _ & HFR2 & _).
assert (VK : forall a0 n v, dsp0 cx - DRAIN_FRAME <= a0 -> a0 + Z.of_nat n <= dsp0 cx ->
  val_mem SEGS (arm W m) a0 n v -> val_mem SEGS (arm W2 m2) a0 n v).
{ intros a0 n v Q1 Q2 Hv. apply (akept_vm W m); [intros x Hx; apply Hfr; clear - Q1 Q2 Hx; lia | exact Hv]. }
assert (SL2 : df_slots cx W2 m2).
{ unfold df_slots. split; [exact HFR2|].
  repeat (split; [apply VK; [unfold DRAIN_FRAME; clear; lia | unfold DRAIN_FRAME; simpl Z.of_nat; clear; lia
    | assumption]|]).
  apply VK; [unfold DRAIN_FRAME; clear; lia | unfold DRAIN_FRAME; simpl Z.of_nat; clear; lia | assumption]. }
(* ---- the splitter: the NUL byte pushes the partial line and resets the state ---- *)
pose proof (df_step_push h1 Hov) as STP.
pose proof (df_firstn_nth_app (ddata s1) k 0 Hnth) as HFS.
assert (FEED1 : feed (drain_b_c.ds_ref s1) (firstn (S k) (ddata s1)) = LS [] false).
{ rewrite HFS, df_feed_snoc, <- Hstate, STP. reflexivity. }
assert (LINES1 : lines (drain_b_c.ds_ref s1) (firstn (S k) (ddata s1)) =
  lines (drain_b_c.ds_ref s1) (firstn k (ddata s1)) ++ [bzs (hs_W h1)]).
{ rewrite HFS, df_lines_snoc, <- Hstate, STP. reflexivity. }
assert (NE : hl_n l2 = hl_n (hs_expected h1) + 1)
  by (unfold hl_n; rewrite Hrecs2, length_app; cbn [length]; clear; lia).
unfold DHIST in HHIST. destruct HHIST as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11).
assert (LD : lines (dSTR cx) (D ++ firstn (S k) (ddata s1)) =
  lines (dSTR cx) (D ++ firstn k (ddata s1)) ++ [bzs (hs_W h1)]).
{ rewrite HFS, app_assoc, df_lines_snoc, feed_app, <- Y2, <- Hstate, STP. reflexivity. }
assert (HH2 : DHIST cx s1 D (D ++ firstn (S k) (ddata s1)) (lines (dSTR cx) D) (lines (dSTR cx) D) h2 LB1 0).
{ unfold DHIST. change (hs_expected h2) with l2.
  pose proof (f_equal (@length _) Y3) as YL. rewrite length_app, !length_map in YL.
  refine (conj Y1 (conj Y2 (conj _ (conj _ (conj _ (conj Y6 (conj Y7 (conj Y8 (conj Y9 (conj Y10 Y11)))))))))).
  - rewrite Hrecs2, map_app, Y3, LD, map_app, <- app_assoc. cbn [map snd]. rewrite df_pu_bzs_inv. reflexivity.
  - rewrite Hrecs2, firstn_app.
    replace (length (hl_recs (hs_expected (dxh cx))) - length (hl_recs (hs_expected h1)))%nat with 0%nat
      by (clear - YL; lia).
    rewrite firstn_O, app_nil_r. exact Y4.
  - rewrite Hcap2, NE. revert Y5 Hncap. clear. unfold hl_n. intros Y5 Hncap. unfold ListRep.grow_cap.
    destruct (Z.eqb_spec (Z.of_nat (length (hl_recs (hs_expected h1)))) (hl_cap (hs_expected h1)));
    [destruct (Z.eqb_spec (hl_cap (hs_expected h1)) 0)|]; cbv iota; lia. }
(* ---- the pushes still to come: the first is this one ---- *)
unfold dpfut in HPFUT. cbv zeta in HPFUT.
rewrite (df_pu_skipn_cons (ddata s1) k 0 Hnth), lines_cons, <- Hstate, STP in HPFUT.
cbn [drain_b_c.pushes_run fst snd] in HPFUT.
destruct HPFUT as (tl2 & HDR & Htl).
rewrite RelayRunT.nret_app, Nat.add_assoc in HDR.
rewrite Htl, <- app_assoc in HBUD.
(* ---- the meter ---- *)
assert (BOV : bsum OV = AREC * hl_cap (hs_expected h1)).
{ unfold OV. destruct (Z.eqb_spec (hl_cap (hs_expected h1)) 0) as [E|E]; unfold bsum; cbn [fold_right snd];
  clear - E; unfold AREC; lia. }
assert (BOV2 : bsum OV2 = AREC * hl_cap l2).
{ unfold OV2. destruct (Z.eqb_spec (hl_cap l2) 0) as [E|E]; unfold bsum; cbn [fold_right snd];
  clear - E; unfold AREC; lia. }
assert (BB1 : blocks_bytes S1 = bsum R0 + AREC * hl_cap (hs_expected h1)).
{ rewrite (blocks_bytes_bsum B ly1 S1), (bsum_perm _ _ P0), bsum_app, BOV. clear; lia. }
assert (BB2 : blocks_bytes S2 = bsum R0 + AREC * ListRep.grow_cap (hl_n (hs_expected h1)) (hl_cap (hs_expected h1)) +
  (Z.of_nat (length (hs_W h1)) + 1)).
{ rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ NP0), bsum_cons, bsum_app, BOV2, Hcap2. cbn [snd].
  clear; lia. }
(* ---- the cut at S k ---- *)
lazymatch type of HDR with
| context [dapush _ (snd (drain_b_c.pushes_run ?N1 ?C1 ?L1 ?J1 ?V1 ?RS1))] =>
  exists out1, ev1, LB1, (spent + lp_cost MT (hs_expected h1) (Z.of_nat (length (hs_W h1)))), J1, ad, V1, RS1,
    (fst (fst (drain_b_c.pushes_run N1 C1 L1 J1 V1 RS1)) ++ tl2), r0, rs0
end.
refine (conj SL2 (conj Hpend (conj Hp0 (conj Hn0 (conj Hdata (conj HMEM2 (conj HnoNUL (conj Hused (conj HSAME
  (conj Hcap (conj Hu (conj Hskip (conj Hkeys (conj Hka (conj Heintr (conj Hpendm (conj Hoff (conj _ (conj _
  (conj _ (conj HH2 (conj HRS (conj _ _))))))))))))))))))))))).
- rewrite FEED1. reflexivity.
- change (hs_expected h2) with l2. rewrite NE, Hen, LINES1, length_app. cbn [length]. clear; lia.
- change (hs_expected h2) with l2. rewrite Hcap2, LINES1, df_pu_pcapm_snoc, Hen, Hecap. apply df_pu_grow_push.
- unfold dpfut. cbv zeta. rewrite LINES1, FEED1, df_pu_pcapm_snoc, df_pu_len_snoc.
  exists tl2. split; [exact HDR | reflexivity].
- eapply (df_pu_bud cx S1 S2 spent (hs_expected h1)); [exact HBUD | exact Hen | exact Hecap
    | unfold bzs; rewrite length_map; reflexivity | clear; lia | rewrite <- Hecap; exact HC0
    | exact Hmle2 | exact BB1 | exact BB2].
Qed.

(* ---- The arms of the body, as runs of the symbolic engine from the loop head to the tail 0x83544. ---- *)
Lemma df_cutjh_journal : forall cx s1 D k p0 ly1 S1 k1 W m md e1 h1,
df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 W m md k1.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md e1 h1 HC.
exact (df_cutj_journal cx s1 D k p0 ly1 S1 k1 W m md (ex_intro _ e1 (ex_intro _ h1 HC))).
Qed.

Lemma df_regs_keep : forall cx s1 p0 k regs regs',
df_regs cx s1 p0 k regs ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 18 = getr regs 18 -> getr regs' 9 = getr regs 9 -> getr regs' 8 = getr regs 8 ->
getr regs' 21 = getr regs 21 -> getr regs' 23 = getr regs 23 -> getr regs' 19 = getr regs 19 ->
getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 -> getr regs' 24 = getr regs 24 ->
getr regs' 20 = getr regs 20 -> getr regs' 27 = getr regs 27 -> getr regs' 22 = getr regs 22 ->
df_regs cx s1 p0 k regs'.
Proof.
intros cx s1 p0 k regs regs' (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22)
  E2 E3 E4 E18 E9 E8 E21 E23 E19 E25 E26 E24 E20 E27 E22.
unfold df_regs, spZ in *. rewrite E2, E3, E4, E18, E9, E8, E21, E23, E19, E25, E26, E24, E20, E27, E22.
repeat split; assumption.
Qed.

(* the windows the arms' regions may write: the g_s fields 48..60 of slot j and the one byte at atom 36 *)
Definition df_win_ok (rs : smem) : bool :=
forallb (fun r => (YP09.r_wlo r =? YP09.r_whi r) ||
  match YP09.r_base r with
  | Some 23%nat => (48 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 60)
  | Some 36%nat => (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 1)
  | _ => false
  end) rs.

Lemma df_wrange : forall E rs a, df_win_ok rs = true -> in_wrange E rs a ->
(bv_unsigned (ew E 23) + 48 <= a < bv_unsigned (ew E 23) + 60) \/ a = bv_unsigned (ew E 36).
Proof.
intros E rs a Hok (r & Hin & Hr). unfold df_win_ok in Hok. rewrite forallb_forall in Hok.
specialize (Hok r Hin). apply orb_prop in Hok as [Hok | Hok].
- apply Z.eqb_eq in Hok. lia.
- destruct (YP09.r_base r) as [[|n]|] eqn:Eb; try discriminate.
  do 22 (destruct n as [|n]; [discriminate|]).
  destruct n as [|n].
  + apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    cbn [base_val] in Hr. left. lia.
  + do 12 (destruct n as [|n]; [discriminate|]).
    destruct n as [|n]; [|discriminate].
    apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    cbn [base_val] in Hr. right. lia.
Qed.

(* the same with only g_s windows (no store through atom 36) *)
Definition df_win_gs (rs : smem) : bool :=
forallb (fun r => (YP09.r_wlo r =? YP09.r_whi r) ||
  match YP09.r_base r with
  | Some 23%nat => (48 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 60)
  | _ => false
  end) rs.

Lemma df_wrange_gs : forall E rs a, df_win_gs rs = true -> in_wrange E rs a ->
bv_unsigned (ew E 23) + 48 <= a < bv_unsigned (ew E 23) + 60.
Proof.
intros E rs a Hok (r & Hin & Hr). unfold df_win_gs in Hok. rewrite forallb_forall in Hok.
specialize (Hok r Hin). apply orb_prop in Hok as [Hok | Hok].
- apply Z.eqb_eq in Hok. lia.
- destruct (YP09.r_base r) as [[|n]|] eqn:Eb; try discriminate.
  do 22 (destruct n as [|n]; [discriminate|]).
  destruct n as [|n]; [|discriminate].
  apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [base_val] in Hr. lia.
Qed.

(* a run whose only windows are slot j's fields writes only walk globals *)
Lemma df_awr_gs : forall E rs STK sp0 FP bl0 blc ly own,
df_win_gs rs = true -> rg_s RG <= bv_unsigned (ew E 23) -> bv_unsigned (ew E 23) + ASRC <= rg_s RG + 4 * ASRC ->
awr_ok_x E rs (G_DR B RG) 0 [] STK sp0 FP bl0 blc ly own.
Proof.
intros E rs STK sp0 FP bl0 blc ly own Hok H1 H2 a Ha.
pose proof (df_wrange_gs E rs a Hok Ha) as Hw.
right; left. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold ASRC in *. lia.
Qed.

(* the walk's view of memory across one more run, outside the bytes P the runs may write *)
Lemma df_meq_step : forall Ek rs (H : word -> bool) m mc mn (P : Z -> Prop),
(forall x : word, ~ P (bv_unsigned x) -> mrestrict H mc x = mrestrict H m x) ->
frame_of Ek rs (mrestrict H mc) (mrestrict H mn) ->
(forall a, in_wrange Ek rs a -> P a) ->
forall x : word, ~ P (bv_unsigned x) -> mrestrict H mn x = mrestrict H m x.
Proof.
intros Ek rs H m mc mn P HM HF Hw x Hx. rewrite <- (HM x Hx). apply HF.
intros Hin. exact (Hx (Hw _ Hin)).
Qed.

Lemma df_keep_of_meq : forall (W : world SEGS) m m' (P : Z -> Prop),
(forall x : word, ~ P (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> abyte_kept W m W m' a.
Proof.
intros W m m' P HM HP a Ha H1. split.
- apply aview_eq_of. apply HM; rewrite unsigned_lit_small by lia; assumption.
- unfold arm. apply (writable_kept (w_H W) m m' a (HP a)).
Qed.

(* aout_at's three cells off G_DR: image bytes (HGO), so addresses, and outside g_s (HRGD) *)
Lemma df_cells_out : forall a,
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_client RG <= a < rg_client RG + 4) \/
(rg_send_dead RG <= a < rg_send_dead RG + 1) ->
0 <= a < 2 ^ 64 /\ ~ (rg_s RG <= a < rg_s RG + 4 * ASRC) /\ in_img SEGS a.
Proof.
intros a Ha.
assert (Hi : in_img SEGS a).
{ apply (proj1 (HGO a ltac:(unfold inG; destruct Ha as [H|[H|H]];
    [apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd
    | apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd]; unfold in_zr; cbn [fst snd]; lia))). }
pose proof (pa_img_range a Hi) as Hr.
df_pu_zd 2%nat 3%nat D3. df_pu_zd 2%nat 6%nat D6. df_pu_zd 2%nat 7%nat D7.
split; [lia|]. split; [|exact Hi]. clear - Ha D3 D6 D7. lia.
Qed.

(* The end of an arm that wrote only h->npartial and h->overlong (skip, long, reset): the cut after the byte,
   then the tail. *)
Lemma df_finish_nw : forall cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b regs' m' md' np2 ovl2 Q,
DBASE B MT MMAX RG cx -> df_regs cx s1 p0 k regs' -> Z.of_nat k < dnum s1 ->
df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 W m' md' k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) -> abyte_kept W m W m' a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
val_mem SEGS (arm W m') (dHA RG cx + 48) 8 np2 -> val_mem SEGS (arm W m') (dHA RG cx + 56) 4 ovl2 ->
0 <= np2 <= APARTIAL -> (ovl2 = 0 \/ ovl2 = 1) ->
hs_state (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
  (hs_pjunk h1) np2 ovl2 (hs_pad h1) (hs_expected h1) (hs_held h1)) = fst (step (hs_state h1) b) ->
snd (step (hs_state h1) b) = None ->
~ In (Z_to_bv 8 0) (firstn (Z.to_nat np2) (hs_pjunk h1)) ->
(forall W2 c2, DRB B MT MMAX RG cx s1 D (S k) W2 c2 -> SRr SEGS W2 c2 Q) ->
(forall W2 c2, DE B MT MMAX RG cx s1 D W2 c2 -> SRr SEGS W2 c2 Q) ->
SRr SEGS W (cfg_at SEGS (BASE + A_df_tail) regs' m' md') Q.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b regs' m' md' np2 ovl2 Q HB HR' Hk HC Hb HJ' KEEP PR
  V48 V56 Hnp2 Hov2 Hst Hnone HW0 Hnext Hend.
set (h2 := HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
  (hs_pjunk h1) np2 ovl2 (hs_pad h1) (hs_expected h1) (hs_held h1)) in *.
pose proof HGSB as (HGlo & HGhi & HGal).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
pose proof HC as HC0.
destruct HC as (out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 & _ & _ & _ & _ & _ & HMEM & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _).
assert (HAR : AR SEGS B ly1 S1 W m md) by (eapply ajournal_gx_AR; exact HJ).
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Apb & Apj & Apg & _).
assert (HAe : dHA RG cx = rg_s RG + ASRC * Z.of_nat (dxj cx)) by reflexivity.
assert (HAlo : rg_s RG <= dHA RG cx) by (rewrite HAe; unfold ASRC; lia).
assert (HAhi : dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (rewrite HAe; unfold ASRC in *; lia).
assert (Hsrc2 : asrc_at B ly1 S1 W m' (dHA RG cx) h2).
{ apply (df_asrc_upd ly1 S1 W m md m' (dHA RG cx) h1 h2 HAR Hsrc HAlo HAhi).
  - intros x Hx H1 _. exact (KEEP x Hx H1).
  - exact PR.
  - exact V48.
  - exact V56.
  - exact Hnp2.
  - exact Hov2.
  - exact Apj.
  - apply (akept_garr8 W m); [|exact Apg]. intros x Hx.
    unfold bzs in Hx. rewrite length_map in Hx. change (hs_pjunk h2) with (hs_pjunk h1) in Hx. rewrite Apj in Hx.
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
    assert (Hx' : hs_partial h1 <= x < hs_partial h1 + APARTIAL) by lia.
    apply KEEP.
    + exact (df_blk_rng ly1 S1 W m md _ _ x HAR Apb Hx').
    + intros Hg. apply (df_blk_gs ly1 S1 W m md _ _ x HAR Apb Hx'). unfold ASRC in *. lia.
  - exact HW0.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity. }
apply (df_tail cx s1 D k p0 W regs' m' md' Q HR'); [| lia | exact Hnext | exact Hend].
exists ly1, S1, k1, e1, h2.
apply (df_close_local cx s1 D k p0 ly1 S1 k1 W m md e1 h1 m' md' h2 b HB HC0 HJ').
- intros x Hx H1 _. exact (KEEP x Hx H1).
- intros x Hx. destruct (df_cells_out x Hx) as (Hr & Hng & _). apply KEEP; [exact Hr|].
  intros Hg. apply Hng. unfold ASRC in *. lia.
- exact PR.
- exact Hsrc2.
- exact Hb.
- exact Hst.
- exact Hnone.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

(* ---- The ordinary arm's partial buffer: byte i replaced. ---- *)
Fixpoint df_updb (l : list byte) (i : nat) (v : byte) : list byte :=
match l, i with
| [], _ => []
| _ :: r, O => v :: r
| x :: r, S i => x :: df_updb r i v
end.

Lemma df_updb_bzs : forall l i v, bzs (df_updb l i v) = YI0t.updn (bzs l) i (bz v).
Proof. unfold bzs. induction l as [|x r IH]; intros [|i] v; cbn; try rewrite IH; reflexivity. Qed.

Lemma df_updb_len : forall l i v, length (df_updb l i v) = length l.
Proof. induction l as [|x r IH]; intros [|i] v; cbn; try rewrite IH; reflexivity. Qed.

Lemma df_updb_firstn : forall l i v, firstn i (df_updb l i v) = firstn i l.
Proof. induction l as [|x r IH]; intros [|i] v; cbn; try rewrite IH; reflexivity. Qed.

Lemma df_updb_nth : forall l i v, (i < length l)%nat -> nth_error (df_updb l i v) i = Some v.
Proof.
induction l as [|x r IH]; intros [|i] v Hi; cbn [length] in Hi; [lia | lia | reflexivity |].
cbn [df_updb nth_error]. apply IH. lia.
Qed.

(* The end of the ordinary arm: h->partial[np] = b, h->npartial = np + 1. *)
Lemma df_finish_add : forall cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b regs' m' md' Q,
DBASE B MT MMAX RG cx -> df_regs cx s1 p0 k regs' -> Z.of_nat k < dnum s1 ->
df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
b <> 0 -> hs_overlong h1 = 0 -> hs_npartial h1 <> APARTIAL ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 W m' md' k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) -> a <> hs_partial h1 + hs_npartial h1 ->
   abyte_kept W m W m' a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
val_mem SEGS (arm W m') (dHA RG cx + 48) 8 (hs_npartial h1 + 1) ->
val_mem SEGS (arm W m') (dHA RG cx + 56) 4 0 ->
val_mem SEGS (arm W m') (hs_partial h1 + hs_npartial h1) 1 b ->
(forall W2 c2, DRB B MT MMAX RG cx s1 D (S k) W2 c2 -> SRr SEGS W2 c2 Q) ->
(forall W2 c2, DE B MT MMAX RG cx s1 D W2 c2 -> SRr SEGS W2 c2 Q) ->
SRr SEGS W (cfg_at SEGS (BASE + A_df_tail) regs' m' md') Q.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b regs' m' md' Q HB HR' Hk HC Hb Hb0 Hov0 HnpA HJ' KEEP PR
  V48 V56 Vb Hnext Hend.
destruct (df_src_byte cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b HC Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & Hb8).
pose proof HC as HC0.
destruct HC as (out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 & _ & _ & _ & _ & _ & HMEM & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _).
assert (HAR : AR SEGS B ly1 S1 W m md) by (eapply ajournal_gx_AR; exact HJ).
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Anp & Aovl & Apb & Apj & Apg & AnoW & _).
assert (HAe : dHA RG cx = rg_s RG + ASRC * Z.of_nat (dxj cx)) by reflexivity.
pose proof HGSB as (HGlo & HGhi & HGal).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
assert (HAlo : rg_s RG <= dHA RG cx) by (rewrite HAe; unfold ASRC; lia).
assert (HAhi : dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (rewrite HAe; unfold ASRC in *; lia).
set (np := hs_npartial h1) in *.
assert (Hnp : 0 <= np < APARTIAL) by (unfold APARTIAL in *; lia).
set (i := Z.to_nat np).
assert (Hi : (i < length (hs_pjunk h1))%nat) by (unfold i, APARTIAL in *; lia).
assert (Hiz : Z.of_nat i = np) by (unfold i; lia).
set (pj2 := df_updb (hs_pjunk h1) i (Z_to_bv 8 b)).
set (h2 := HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
  pj2 (np + 1) 0 (hs_pad h1) (hs_expected h1) (hs_held h1)).
assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) ->
  ~ (hs_partial h1 <= a < hs_partial h1 + APARTIAL) -> abyte_kept W m W m' a).
{ intros x Hx H1 H2. apply KEEP; [exact Hx | exact H1 |]. intros ->. apply H2. lia. }
assert (Hpw : hs_W h2 = firstn i (hs_pjunk h1) ++ [Z_to_bv 8 b]).
{ unfold hs_W. cbn [hs_pjunk hs_npartial h2]. replace (Z.to_nat (np + 1)) with (S i) by (unfold i; lia).
  rewrite (df_firstn_nth_app pj2 i (Z_to_bv 8 b) (df_updb_nth _ _ _ Hi)). unfold pj2. rewrite df_updb_firstn.
  reflexivity. }
assert (Hsrc2 : asrc_at B ly1 S1 W m' (dHA RG cx) h2).
{ apply (df_asrc_upd ly1 S1 W m md m' (dHA RG cx) h1 h2 HAR Hsrc HAlo HAhi KX PR V48 V56).
  - cbn [hs_npartial h2]. unfold APARTIAL in *. lia.
  - left. reflexivity.
  - cbn [hs_pjunk h2]. unfold pj2. rewrite df_updb_len. exact Apj.
  - cbn [hs_pjunk h2]. unfold pj2. rewrite df_updb_bzs.
    assert (Hbz : bz (Z_to_bv 8 b) = b) by exact (df_bz_of b Hb8).
    rewrite Hbz.
    apply (garr8_upd SEGS (arm W m) (arm W m') (hs_partial h1) (bzs (hs_pjunk h1)) i b Apg).
    + unfold bzs. rewrite length_map. exact Hi.
    + rewrite Hiz. exact Vb.
    + exact Hb8.
    + intros x Hx Hne. unfold arm. apply (mbyte_of_aview SEGS).
      unfold bzs in Hx. rewrite length_map, Apj in Hx.
      assert (Hx' : hs_partial h1 <= x < hs_partial h1 + APARTIAL) by lia.
      apply (proj1 (KEEP x (df_blk_rng ly1 S1 W m md _ _ x HAR Apb Hx') ltac:(intros Hg;
        apply (df_blk_gs ly1 S1 W m md _ _ x HAR Apb Hx'); unfold ASRC in *; lia) ltac:(rewrite <- Hiz; exact Hne))).
  - rewrite Hpw. intros Hin. apply in_app_or in Hin as [Hin | [Hin | []]].
    + apply AnoW. unfold hs_W. exact Hin.
    + apply Hb0. apply (f_equal bz) in Hin. rewrite (df_bz_of b Hb8), (df_bz_of 0 ltac:(lia)) in Hin. exact Hin.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity. }
apply (df_tail cx s1 D k p0 W regs' m' md' Q HR'); [| lia | exact Hnext | exact Hend].
exists ly1, S1, k1, e1, h2.
apply (df_close_local cx s1 D k p0 ly1 S1 k1 W m md e1 h1 m' md' h2 b HB HC0 HJ').
- exact KX.
- intros x Hx. destruct (df_cells_out x Hx) as (Hr & Hng & Himg). apply KEEP; [exact Hr | |].
  + intros Hg. apply Hng. unfold ASRC in *. lia.
  + intros ->. pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & HrqA).
    apply (blk_img SEGS B LAWS ly1 S1 W m md (hs_partial h1) APARTIAL (hs_partial h1 + np) HAR Apb); [|exact Himg].
    clear - Hnp HrqA. lia.
- exact PR.
- exact Hsrc2.
- exact Hb.
- rewrite (df_step_add h1 b Hb0 Hov0 HnpA Anp Apj). cbn [fst].
  apply (df_state_add h1 h2 b); cbn [hs_overlong hs_npartial hs_pjunk h2].
  + reflexivity.
  + reflexivity.
  + lia.
  + unfold pj2. apply df_updb_firstn.
  + unfold pj2. apply df_updb_nth. exact Hi.
  + exact Hb8.
- rewrite (df_step_add h1 b Hb0 Hov0 HnpA Anp Apj). reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

(* the bytes an arm that pushes nothing writes: slot j's fields 48..60 *)
Definition df_Pg (HA a : Z) : Prop := HA + 48 <= a < HA + 60.

Lemma df_U0 : forall E, U E (SLit 0) = 0.
Proof. intros E. rewrite U_SLit. reflexivity. Qed.

Lemma df_cutjh_src : forall cx s1 D k p0 ly1 S1 k1 W m md e1 h1,
df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 -> asrc_at B ly1 S1 W m (dHA RG cx) h1.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md e1 h1 HC.
destruct HC as (out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 & _ & _ & _ & _ & _ & HMEM & _).
exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMEM))))))))).
Qed.

(* a run's write permission when the regions write only slot j's fields *)
Ltac df_awr U23 HAe :=
apply df_awr_gs; [vm_compute; reflexivity
  | cbn [ew ewset Nat.eqb]; rewrite U23, HAe; unfold ASRC in *; lia
  | cbn [ew ewset Nat.eqb]; rewrite U23, HAe; unfold ASRC in *; lia].

(* carry "the walk's view outside df_Pg is m's" and "m's present bytes are present" across the last run *)
Ltac df_track m MEQ PR U23 :=
lazymatch goal with
| HF : frame_of ?Ex ?rs (mrestrict ?Hh ?mc) (mrestrict ?Hh ?mn),
  HGr : mem_grows (mrestrict ?Hh ?mc) (mrestrict ?Hh ?mn) |- _ =>
  let MEQ' := fresh "MEQ" in let PR' := fresh "PR" in
  pose proof (df_meq_step Ex rs Hh m mc mn _ MEQ HF
    ltac:(intros a Ha; pose proof (df_wrange_gs Ex rs a ltac:(vm_compute; reflexivity) Ha) as Hw;
          cbn [ew ewset Nat.eqb] in Hw; rewrite U23 in Hw; exact Hw)) as MEQ';
  assert (PR' : forall a, apresent Hh m a -> apresent Hh mn a)
    by (intros a Ha; exact (apresent_grows Hh mc mn a HGr (PR a Ha)));
  clear MEQ PR; rename MEQ' into MEQ; rename PR' into PR;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
end.

(* rewrite the denotation of an extra atom inside a branch condition, whatever the run's environment *)
Ltac df_Uat Hc n v Ev Rv :=
lazymatch type of Hc with context [U ?Ex (SOff n 0)] =>
  rewrite (U_atom Ex n v ltac:(cbn [ew ewset Nat.eqb]; exact Ev) Rv) in Hc
end.

Lemma df_ovl_nz : forall o, o = 0 \/ o = 1 -> negb (o =? 0) = true -> o = 1.
Proof. intros o [-> | ->] H; [discriminate | reflexivity]. Qed.

Lemma df_ovl_z : forall o, negb (o =? 0) = false -> o = 0.
Proof. intros o H. apply negb_false_iff, Z.eqb_eq in H. exact H. Qed.

Lemma df_U6000 : forall E, U E (SLit 6000) = 6000.
Proof. intros E. rewrite U_SLit. reflexivity. Qed.

Lemma df_den0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. transitivity (ew E n); [|exact H]. cbn. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma df_reg_atom : forall Ex (regs' regs : bvmap 5 word) (r r0 : bv 5) n,
getr regs' r = sv_denot Ex (SOff n 0) -> ew Ex n = getr regs r0 -> getr regs' r = getr regs r0.
Proof.
intros Ex regs' regs r r0 n H1 H2. rewrite H1, <- H2. cbn. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma df_reg_shv : forall Ex (regs' : bvmap 5 word) (r : bv 5) n c v,
getr regs' r = sv_denot Ex (df_shv n c) -> ew Ex n = Z_to_bv 64 v -> ew Ex 21 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> getr regs' r = w64 (shadow_addr (v + c)).
Proof. intros Ex regs' r n c v H Hn H21 Hv Hc. rewrite H. apply df_den_shadow; assumption. Qed.

(* a register's value in the run's final state, as the symbolic state names it *)
Ltac df_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
end.

Ltac df_ra HS EE n r :=
let Q := fresh "Q" in df_reg HS r Q;
apply (df_reg_atom _ _ _ _ _ n Q); cbn [ew ewset Nat.eqb]; exact (EE n r eq_refl).

Ltac df_rs HS E23 E21 HAr r c Rr :=
let Q := fresh "Q" in df_reg HS r Q; rewrite Rr;
apply (df_reg_shv _ _ r 23%nat c _ Q);
[ cbn [ew ewset Nat.eqb]; exact E23 | cbn [ew ewset Nat.eqb]; exact E21
| clear - HAr; lia | clear - HAr; lia ].

(* the loop's registers are the body's callee-kept ones: the body writes only a0..a3 *)
Ltac df_regs_tac HS HR EE E23 E21 HAr R20 R27 R22 :=
apply (df_regs_keep _ _ _ _ _ _ HR);
[ df_ra HS EE 2%nat (2%bv : bv 5) | df_ra HS EE 3%nat (3%bv : bv 5) | df_ra HS EE 4%nat (4%bv : bv 5)
| df_ra HS EE 18%nat (18%bv : bv 5) | df_ra HS EE 9%nat (9%bv : bv 5) | df_ra HS EE 8%nat (8%bv : bv 5)
| df_ra HS EE 21%nat (21%bv : bv 5) | df_ra HS EE 23%nat (23%bv : bv 5) | df_ra HS EE 19%nat (19%bv : bv 5)
| df_ra HS EE 25%nat (25%bv : bv 5) | df_ra HS EE 26%nat (26%bv : bv 5) | df_ra HS EE 24%nat (24%bv : bv 5)
| df_rs HS E23 E21 HAr (20%bv : bv 5) 40 R20 | df_rs HS E23 E21 HAr (27%bv : bv 5) 48 R27
| df_rs HS E23 E21 HAr (22%bv : bv 5) 56 R22 ].

(* an arm's end: run to the tail 0x83544, carry the memory facts, name slot j's region (index i of the final
   state's regions) RG1, and put the goal in mkst form *)
Ltac df_leaf_run HS HJ SHOK U23 HAe m MEQ PR i :=
paj_run_to_tok RUNTO HS HJ SHOK DFspan A_df_tail; [df_awr U23 HAe|];
df_track m MEQ PR U23;
let RG1 := fresh "RG1" in
pose proof (st_ok_pi_region_nth _ _ _ i _ HS eq_refl) as RG1; cbn [ms_mem restrict] in RG1;
pmkst HS.

Ltac df_inc := repeat (first [left; reflexivity | right]).

(* a field of slot j in the final state; left: its denotation and its range *)
Ltac df_v HA U23 od w e v :=
lazymatch goal with RG1 : region_ok _ _ _ (YP09.mkRegion (Some 23%nat) _ _ _ _ _) |- _ =>
unfold arm; eapply (field_of_region _ _ 23%nat HA _ _ _ _ _ od w e v RG1);
[ cbn [ew ewset Nat.eqb]; exact U23 | cbn [In]; df_inc | | | cbn; lia ]
end.

(* a live block's byte is kept by a run that writes only slot j's fields 48..60 *)
Lemma df_heap_keep : forall ly S (W : world SEGS) m md m' HA p n a,
AR SEGS B ly S W m md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
(forall x : word, ~ df_Pg HA (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
(forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
abyte_kept W m W m' a.
Proof.
intros ly S W m md m' HA p n a HAR Hin Ha HAlo HAhi HM HP.
destruct (al_blocks SEGS B LAWS ly S W m md p n HAR Hin) as (_ & H4 & Hc & _).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
apply (df_keep_of_meq W m m' (df_Pg HA) HM HP a); [clear - Ha H4 Hc ACL; lia|].
intros Hg. apply (blk_img SEGS B LAWS ly S W m md p n a HAR Hin Ha).
unfold df_Pg in Hg.
apply (proj1 (HG a ltac:(unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
  unfold ASRC in HAlo, HAhi |- *; clear - Hg HAlo HAhi; lia))).
Qed.

Lemma df_heap_np : forall ly S (W : world SEGS) m md HA p n a,
AR SEGS B ly S W m md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
(0 <= a < 2 ^ 64) /\ ~ df_Pg HA a.
Proof.
intros ly S W m md HA p n a HAR Hin Ha HAlo HAhi.
destruct (al_blocks SEGS B LAWS ly S W m md p n HAR Hin) as (_ & H4 & Hc & _).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
split; [clear - Ha H4 Hc ACL; lia|].
intros Hg. apply (blk_img SEGS B LAWS ly S W m md p n a HAR Hin Ha).
unfold df_Pg in Hg.
apply (proj1 (HG a ltac:(unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
  unfold ASRC in HAlo, HAhi |- *; clear - Hg HAlo HAhi; lia))).
Qed.

(* an image byte off slot j's fields 48..60 is kept by such a run *)
Lemma df_img_np : forall HA a, in_img SEGS a -> ~ (HA + 48 <= a < HA + 60) -> (0 <= a < 2 ^ 64) /\ ~ df_Pg HA a.
Proof.
intros HA a Hi Hn. pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
split; [clear - Hlow; lia | exact Hn].
Qed.

(* aout_at's three cells: addresses off g_s, image bytes off the allocator's statics and off errno *)
Lemma df_cell_facts : forall a,
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_client RG <= a < rg_client RG + 4) \/
(rg_send_dead RG <= a < rg_send_dead RG + 1) ->
0 <= a < 2 ^ 64 /\ ~ (rg_s RG <= a < rg_s RG + 4 * ASRC) /\ in_img SEGS a /\
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. destruct (df_cells_out a Ha) as (H1 & H2 & H3).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
- apply (proj1 (proj2 (HGO a ltac:(unfold inG; destruct Ha as [H|[H|H]];
    [apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd
    | apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd]; unfold in_zr; cbn [fst snd]; lia)))).
- df_pu_zd 3%nat 11%nat D3. df_pu_zd 6%nat 11%nat D6. df_pu_zd 7%nat 11%nat D7.
  clear - Ha D3 D6 D7. lia.
Qed.

(* errno's four bytes: image bytes (errno is in G_DR) off g_s *)
Lemma df_errno_facts : forall a, as_errno B <= a < as_errno B + 4 ->
0 <= a < 2 ^ 64 /\ ~ (rg_s RG <= a < rg_s RG + 4 * ASRC) /\ in_img SEGS a.
Proof.
intros a Ha.
assert (Hi : in_img SEGS a)
  by (apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; do 6 apply Exists_cons_tl; apply Exists_cons_hd; exact Ha)))).
pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
df_pu_zd 2%nat 11%nat D.
split; [clear - Hlow; lia|]. split; [clear - D Ha; lia | exact Hi].
Qed.

Lemma df_hsW_len : forall h, 0 <= hs_npartial h <= APARTIAL -> Z.of_nat (length (hs_pjunk h)) = APARTIAL ->
Z.of_nat (length (hs_W h)) = hs_npartial h.
Proof. intros h Hn Hl. unfold hs_W. rewrite length_firstn. unfold APARTIAL in *. lia. Qed.
(* ---- df_push_pre's helpers.  The requests still to come ask for no negative size (SlotP4Res3Aux.v drain_inv's
   invariant over the model: the three capacities stay >= 0), so their cost and their bytes are >= 0. ---- *)
Definition df_evnn {P : Type} (ev : RelayRunT.rev P) : Prop :=
match ev with
| RelayRunT.RMalloc n => 0 <= n
| RelayRunT.RFree _ _ => True
| RelayRunT.RRealloc _ n _ => 0 <= n
end.

Lemma df_tnn_cost : forall (t : dtrace), Forall df_evnn t -> 0 <= tr_cost MT t.
Proof.
intros t H. pose proof (mo_free_nonneg MT MTL) as F0.
induction H as [|ev t Hev _ IH]; [unfold tr_cost; cbn [fold_right]; lia|].
destruct ev as [n|n a|kk n a]; cbn [df_evnn] in Hev; unfold tr_cost in IH |- *; cbn [fold_right].
- pose proof (mo_malloc_nonneg MT MTL n Hev). lia.
- lia.
- pose proof (mo_malloc_nonneg MT MTL n Hev). lia.
Qed.

Lemma df_tnn_alloc : forall (t : dtrace), Forall df_evnn t -> 0 <= tr_alloc t.
Proof.
intros t H. induction H as [|ev t Hev _ IH]; [unfold tr_alloc; cbn [fold_right]; lia|].
destruct ev as [n|n a|kk n a]; cbn [df_evnn] in Hev; unfold tr_alloc in IH |- *; cbn [fold_right]; lia.
Qed.

Lemma df_tnn_lpt : forall (v : dadrF) N C n, 0 <= C -> 0 <= n -> Forall df_evnn (ListTr.list_push_tra v N C n).
Proof.
intros v N C n HC Hn. unfold ListTr.list_push_tra. apply Forall_app. split.
- destruct (N =? C); [destruct (C =? 0)|]; cbn; repeat constructor; cbn [df_evnn]; lia.
- constructor; [cbn [df_evnn]; lia | constructor].
Qed.

Lemma df_tnn_drop : forall (a : dadrF) n, Forall df_evnn (ListTr.list_drop_tra a n).
Proof. intros a n. unfold ListTr.list_drop_tra. constructor; [exact I | constructor]. Qed.

Lemma df_push_cap_nn : forall n c, 0 <= c -> 0 <= drain_b_c.push_cap n c.
Proof.
intros n c Hc. unfold drain_b_c.push_cap.
destruct (Z.eqb_spec n c); [destruct (Z.eqb_spec c 0)|]; cbv iota; lia.
Qed.

Lemma df_tnn_pushes : forall ls n cap j v rs, 0 <= cap ->
Forall df_evnn (fst (fst (drain_b_c.pushes_run n cap ls j v rs))) /\
0 <= snd (fst (drain_b_c.pushes_run n cap ls j v rs)).
Proof.
induction ls as [|l r IH]; intros n cap j v rs Hc; cbn [drain_b_c.pushes_run fst snd];
  [split; [constructor | exact Hc]|].
match goal with |- context [drain_b_c.pushes_run (n + 1) _ r ?j1 ?v1 ?rs1] =>
  destruct (IH (n + 1) (drain_b_c.push_cap n cap) j1 v1 rs1 (df_push_cap_nn n cap Hc)) as [T1 C1] end.
split; [apply Forall_app; split; [apply df_tnn_lpt; [exact Hc | lia] | exact T1] | exact C1].
Qed.

Lemma df_pcapm_nn : forall ls n c, 0 <= c -> 0 <= pcapm n c ls.
Proof. intros ls n c Hc. unfold pcapm. exact (proj2 (df_tnn_pushes ls n c _ _ _ Hc)). Qed.

Lemma df_pcapm_neg : forall ls n c, c < 0 -> pcapm n c ls < 0.
Proof.
induction ls as [|l ls IH]; intros n c Hc; [exact Hc|].
rewrite df_pu_pcapm_cons. apply IH. unfold drain_b_c.push_cap.
destruct (Z.eqb_spec n c); [destruct (Z.eqb_spec c 0)|]; cbv iota; lia.
Qed.

Lemma df_tnn_sl : forall f mx no cap rem j o, 0 <= cap ->
Forall df_evnn (fst (send_line_b_c.sl_run f mx no cap rem j o)) /\
0 <= fst (snd (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run];
  [cbn [fst snd]; split; [constructor | exact Hc]|].
destruct (rem <=? 0); [cbn [fst snd]; split; [constructor | exact Hc]|].
match goal with |- context [if cap <? ?b then _ else _] => destruct (Z.ltb_spec cap b) as [Hlt|Hge] end.
- cbn [fst snd].
  match goal with |- context [send_line_b_c.sl_run f mx ?n1 ?c1 ?r1 ?j1 ?o1] =>
    destruct (IH mx n1 c1 r1 j1 o1 ltac:(lia)) as [T1 C1] end.
  split; [constructor; [destruct (cap =? 0); cbn [df_evnn]; lia | exact T1] | exact C1].
- cbn [fst snd]. apply IH. exact Hc.
Qed.

Lemma df_tnn_seen : forall H ka l j ha ks, Forall df_evnn (fst (fst (drain_b_c.seen_tr H ka l j ha ks))).
Proof.
intros H ka l j ha ks. unfold drain_b_c.seen_tr.
destruct (gesture l) as [[[|] x]|]; [destruct (index_of x H)|destruct (index_of x H)|]; cbn [fst];
  repeat apply Forall_cons;
  try first [ apply Forall_nil | exact I | (cbn [df_evnn]; lia) | (destruct (ka =? 0); cbn [df_evnn]; lia) ].
Qed.

Lemma df_tnn_lines : forall live mx ls no cap H ka j o ha ks, 0 <= cap ->
Forall df_evnn (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) /\
0 <= fst (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))).
Proof.
intros live mx ls. induction ls as [|l r IH]; intros no cap H ka j o ha ks Hc;
  cbn [drain_b_c.lines_run fst snd]; [split; [constructor | exact Hc]|].
assert (Hc1 : 0 <= send_line_b_c.send_line_cap live mx no cap (Z.of_nat (length l) + 1)).
{ unfold send_line_b_c.send_line_cap. destruct live; [exact (proj2 (df_tnn_sl _ _ _ _ _ _ _ Hc)) | exact Hc]. }
match goal with |- context [drain_b_c.lines_run live mx ?n1 ?c1 ?H1 ?k1 r ?j1 ?o1 ?ha1 ?ks1] =>
  destruct (IH n1 c1 H1 k1 j1 o1 ha1 ks1 Hc1) as [T1 C1] end.
split; [|exact C1].
apply Forall_app. split; [|apply Forall_app; split; [apply df_tnn_seen | exact T1]].
unfold send_line_b_c.send_line_tr. destruct live; [exact (proj1 (df_tnn_sl _ _ _ _ _ _ _ Hc)) | constructor].
Qed.

Lemma df_tnn_grow : forall cap used j b, 0 <= cap ->
Forall df_evnn (fst (drain_b_c.grow_tr cap used j b)) /\ 0 <= fst (snd (drain_b_c.grow_tr cap used j b)).
Proof.
intros cap used j b Hc. unfold drain_b_c.grow_tr.
destruct (cap - used <? 4096); [|cbn [fst snd]; split; [constructor | exact Hc]].
destruct (Z.eqb_spec cap 0); cbn [fst snd]; (split; [constructor; [cbn [df_evnn]; lia | constructor] | lia]).
Qed.

Lemma df_tnn_drain : forall f lv mx s j a, 0 <= drain_b_c.ds_cap s -> 0 <= drain_b_c.ds_ecap s ->
0 <= drain_b_c.ds_ocap s -> Forall df_evnn (fst (drain_b_c.drain_run f lv mx s j a)).
Proof.
induction f as [|f IH]; intros lv mx s j a Hc He Ho; cbn [drain_b_c.drain_run]; [constructor|].
destruct (df_tnn_grow (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) Hc)
  as [Tg Cg].
destruct (drain_b_c.ds_eintr s).
- cbn [fst]. apply Forall_app. split; [exact Tg|].
  apply IH; cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_ocap]; assumption.
- destruct (drain_b_c.ds_pend s) as [|r0 rs]; [cbn [fst]; exact Tg|].
  match goal with |- context [if ?c <=? 0 then _ else _] => destruct (c <=? 0) end; [cbn [fst]; exact Tg|].
  match goal with |- context [chunk ?u ?sk ?d] => destruct (chunk u sk d) as [[u' sk'] rl] end.
  match goal with |- context [drain_b_c.lines_run ?lv0 ?m ?no ?c ?H ?k rl ?jj ?o ?ha ?ks] =>
    destruct (df_tnn_lines lv0 m rl no c H k jj o ha ks Ho) as [LT LC];
    destruct (snd (fst (drain_b_c.lines_run lv0 m no c H k rl jj o ha ks))) as [[oc' H'] ka'] eqn:E1;
    destruct (snd (drain_b_c.lines_run lv0 m no c H k rl jj o ha ks)) as [[o' ha'] ks'] eqn:E2
  end.
  try rewrite E1 in LC. cbn [fst] in LC.
  match goal with |- context [drain_b_c.pushes_run ?n0 ?c0 ?ls0 ?j0 ?v0 ?rs0] =>
    destruct (df_tnn_pushes ls0 n0 c0 j0 v0 rs0 He) as [PT PC] end.
  cbn [fst snd].
  apply Forall_app. split; [exact Tg|].
  apply Forall_app. split; [exact PT|].
  apply Forall_app. split;
    [match goal with |- Forall _ (if ?w then _ else _) => destruct w; [apply df_tnn_drop | constructor] end|].
  apply Forall_app. split; [exact LT|].
  apply IH; cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_ocap]; assumption.
Qed.

(* the requests after this round's pushes: list_drop, the relay's lines, the later rounds *)
Lemma df_tnn_drfut : forall cx s1 jb (a : drain_b_c.dadr) tl, 0 <= drain_b_c.ds_cap s1 ->
0 <= drain_b_c.ds_ecap s1 -> 0 <= drain_b_c.ds_ocap s1 -> drfut cx s1 jb a tl -> Forall df_evnn tl.
Proof.
intros cx s1 jb a tl Hc He Ho (tl2 & HL & ->).
apply Forall_app. split; [unfold ddrop; destruct (dwhole s1); [apply df_tnn_drop | constructor]|].
unfold dlfut in HL. cbv zeta in HL. destruct HL as (tl3 & HD & ->).
apply Forall_app. split; [exact (proj1 (df_tnn_lines _ _ _ _ _ _ _ _ _ _ _ Ho))|].
destruct HD as (fuel & _ & _ & Ef & _). rewrite <- Ef.
apply df_tnn_drain; unfold dnext; cbn [drain_b_c.ds_cap drain_b_c.ds_ecap drain_b_c.ds_ocap].
- exact Hc.
- exact (df_pcapm_nn _ _ _ He).
- unfold lrun. exact (proj2 (df_tnn_lines _ _ _ _ _ _ _ _ _ _ _ Ho)).
Qed.

(* list_push's own requests: its largest one and its bytes, read as lp_spec states them *)
Lemma df_pp_max : forall (v : dadrF) (l : hlist) n, lp_grow l = true ->
lp_vbytes l <= tr_max (ListTr.list_push_tra v (hl_n l) (hl_cap l) n).
Proof.
intros v l n G. unfold lp_grow in G. unfold lp_vbytes, ListTr.list_push_tra, tr_max, ListRep.grow_cap.
rewrite G. destruct (Z.eqb_spec (hl_cap l) 0); cbn [app fold_right]; unfold AREC; lia.
Qed.

Lemma df_pp_alloc : forall (v : dadrF) (l : hlist) n,
tr_alloc (ListTr.list_push_tra v (hl_n l) (hl_cap l) n) = (if lp_grow l then lp_vbytes l else 0) + (n + 1).
Proof.
intros v l n. rewrite df_pu_lp_alloc. unfold lp_grow, lp_vbytes, ListRep.grow_cap, AREC.
destruct (Z.eqb_spec (hl_n l) (hl_cap l)); [destruct (Z.eqb_spec (hl_cap l) 0)|]; cbv iota; lia.
Qed.

Lemma df_vbytes_nn : forall l, 0 <= hl_cap l -> 0 <= lp_vbytes l.
Proof.
intros l HC. unfold lp_vbytes, AREC, ListRep.grow_cap.
destruct (Z.eqb_spec (hl_n l) (hl_cap l)); [destruct (Z.eqb_spec (hl_cap l) 0)|]; cbv iota; lia.
Qed.

Lemma df_lpcost_nn : forall l n, 0 <= hl_cap l -> 0 <= n -> 0 <= lp_cost MT l n.
Proof.
intros l n HC Hn. pose proof (mo_malloc_nonneg MT MTL (n + 1) ltac:(lia)) as M1.
pose proof (mo_malloc_nonneg MT MTL _ (df_vbytes_nn l HC)) as M2.
pose proof (mo_free_nonneg MT MTL) as F0.
unfold lp_cost. destruct (lp_grow l); lia.
Qed.

Definition df_pair_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma df_nd_fst : forall (A C : list (Z * Z)) x, List.NoDup (map fst (A ++ C)) -> In x A -> ~ In x C.
Proof.
induction A as [|y A IH]; intros C x H HA HC; [destruct HA|].
cbn [app map] in H. apply List.NoDup_cons_iff in H as [Hy H].
destruct HA as [<-|HA]; [|exact (IH C x H HA HC)].
apply Hy. apply in_map. apply in_or_app. right. exact HC.
Qed.

(* ---- The NUL byte with h->overlong = 0: the call list_push (&h->expected, h->partial, h->npartial). ----
   df_push_pre: what lp_spec asks of the call, read off the cut (the source, the budget, the footprint). *)
Lemma df_push_pre : forall cx s1 D k p0 ly1 S1 k1 W m md e1 h1,
DBASE B MT MMAX RG cx -> df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 ->
nth_error (ddata s1) k = Some 0 -> hs_overlong h1 = 0 ->
alist_at B ly1 S1 W m (dHA RG cx + 64) (hs_expected h1) true /\
In (hs_partial h1, APARTIAL) (ablocks B ly1 S1) /\ hs_partial h1 <> hl_v (hs_expected h1) /\
garr8 SEGS (mrestrict (w_H W) m) (hs_partial h1) (bzs (hs_W h1)) /\
~ In (Z_to_bv 8 0) (hs_W h1) /\ Z.of_nat (length (hs_W h1)) <= APARTIAL /\
(lp_grow (hs_expected h1) = true -> lp_vbytes (hs_expected h1) < MMAX) /\
blocks_bytes S1 + tr_peak (lp_tr (hs_expected h1) (Z.of_nat (length (hs_W h1)))) <= LIVE_MAX /\
mo_ok MT S1 (lp_cost MT (hs_expected h1) (Z.of_nat (length (hs_W h1)))) /\
(forall a, inFP (lp_FP (hs_expected h1)) a ->
  (inFP (dFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a).
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md e1 h1 HB HC Hnth Hov.
destruct HC as (out1 & ev1 & LB1 & spent & jb & ad & v0 & rs & tl & r0 & rs0 &
  _ & _ & _ & _ & _ & HMEM & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hstate & Hen & Hecap & _ & HRS & HPFUT & HBUD).
destruct HMEM as (HJ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _ & _ & Hout & _ & Hperm).
destruct Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H16 & _ &
  H18 & _ & H20 & H21 & H22 & _ & H24).
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPerm0 & _ & _ & _ & _ & _ & HMok).
assert (HAR1 : AR SEGS B ly1 S1 W m md) by (eapply ajournal_gx_AR; exact HJ).
clear HJ.
pose proof H22 as (_ & _ & _ & _ & Hncap & Hvdisj & _).
assert (HC0 : 0 <= hl_cap (hs_expected h1)) by (clear - Hncap; unfold hl_n in Hncap; lia).
(* ---- the three capacities of the round state are >= 0 ---- *)
assert (HCP : 0 <= drain_b_c.ds_cap s1) by (destruct HRS as (_ & _ & Rg & _); clear - Rg; unfold ulen in Rg; lia).
assert (HOC : 0 <= drain_b_c.ds_ocap s1).
{ destruct Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & Hoc).
  clear - Hoc. destruct Hoc as [(E & _) | (P & _)]; lia. }
assert (HEC : 0 <= drain_b_c.ds_ecap s1).
{ destruct (Z_lt_le_dec (drain_b_c.ds_ecap s1) 0) as [Hlt|Hge]; [|exact Hge].
  pose proof (df_pcapm_neg (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1))) (drain_b_c.ds_en s1) _ Hlt) as X.
  rewrite <- Hecap in X. clear - X HC0. lia. }
clear Hout HRS.
(* ---- the requests: this push first, then the rest of the round's pushes, then the later requests ---- *)
pose proof (df_step_push h1 Hov) as STP.
unfold dpfut in HPFUT. cbv zeta in HPFUT.
rewrite (df_pu_skipn_cons (ddata s1) k 0 Hnth), lines_cons, <- Hstate, STP in HPFUT.
cbn [drain_b_c.pushes_run fst snd] in HPFUT.
destruct HPFUT as (tl2 & HDR & Htl).
pose proof (df_tnn_drfut cx s1 _ _ tl2 HCP HEC HOC HDR) as TN3.
clear HDR.
rewrite <- Hen, <- Hecap in Htl.
assert (ELW : length (bzs (hs_W h1)) = length (hs_W h1)) by (unfold bzs; apply length_map).
rewrite ELW in Htl.
lazymatch type of Htl with
| _ = (_ ++ fst (fst (drain_b_c.pushes_run ?n1 ?c1 ?ls1 ?j1 ?v1 ?rs1))) ++ _ =>
  pose proof (proj1 (df_tnn_pushes ls1 n1 c1 j1 v1 rs1
    (df_push_cap_nn (hl_n (hs_expected h1)) (hl_cap (hs_expected h1)) HC0))) as TN2
end.
pose proof (df_tnn_cost _ TN2) as C2. pose proof (df_tnn_cost _ TN3) as C3.
pose proof (mo_free_nonneg MT MTL) as F0.
pose proof (df_lpcost_nn (hs_expected h1) (Z.of_nat (length (hs_W h1))) HC0 (Nat2Z.is_nonneg _)) as LC0.
lazymatch type of Htl with
| _ = (?T1 ++ ?T2) ++ _ =>
  rewrite Htl in HBUD; clear Htl;
  destruct HBUD as (Bl & _ & Bc & Ba & Bm);
  rewrite (df_pu_tr_cost_app (T1 ++ T2) tl2), (df_pu_tr_cost_app T1 T2) in Bc;
  rewrite <- app_assoc in Ba;
  rewrite (df_pu_tr_max_app (T1 ++ T2) tl2), (df_pu_tr_max_app T1 T2) in Bm
end.
rewrite <- (df_pu_lp_cost (hs_expected h1) v0 (Z.of_nat (length (hs_W h1)))) in Bc.
match type of Ba with _ + tr_peak (?T1 ++ ?R) <= _ => pose proof (W_tr_peak.tr_peak_prefix T1 R) as Ba1 end.
refine (conj H22 (conj H18 (conj _ (conj _ (conj H21 (conj _ (conj _ (conj _ (conj _ _))))))))).
- (* h->partial is not the expected list's vector *)
  intros Heq. destruct Hvdisj as [(Hc0 & Hv0) | (Hcp & _)].
  + destruct (al_blocks SEGS B LAWS ly1 S1 W m md _ _ HAR1 H18) as (_ & H4096 & _).
    clear - H4096 Heq Hv0. lia.
  + apply NoDup_ListNoDup in H24. unfold hs_blocks in H24. cbn [app] in H24.
    apply List.NoDup_remove_2 in H24. apply H24. apply in_or_app. right. apply in_or_app. left.
    rewrite Heq. unfold list_blocks.
    rewrite (proj2 (Z.eqb_neq (hl_cap (hs_expected h1)) 0) ltac:(clear - Hcp; lia)).
    left. reflexivity.
- (* the partial line's bytes: the first npartial of the buffer *)
  unfold hs_W. rewrite <- (firstn_skipn (Z.to_nat (hs_npartial h1)) (hs_pjunk h1)) in H20.
  unfold bzs in H20 |- *. rewrite map_app in H20. exact (proj1 (proj1 (garr8_app _ _ _ _ _) H20)).
- assert (LW : (length (hs_W h1) <= Z.to_nat (hs_npartial h1))%nat)
    by (unfold hs_W; rewrite length_firstn; apply Nat.le_min_l).
  clear - LW H16. unfold APARTIAL in *. lia.
- intros G. pose proof (df_pp_max v0 (hs_expected h1) (Z.of_nat (length (hs_W h1))) G) as X.
  clear - X Bm. lia.
- (* C3: list_push's requests open the trace still owed, so their peak is within that trace's (W_tr_peak.v
     tr_peak_prefix; the requests' sizes do not depend on the names, list_push_tra_sz) *)
  unfold lp_tr.
  destruct (W_tr_peak.tr_sz_measures _ _ (W_tr_peak.list_push_tra_sz v0 RelayRunF.adr0 (hl_n (hs_expected h1))
    (hl_cap (hs_expected h1)) (Z.of_nat (length (hs_W h1))))) as (E & _).
  rewrite <- E. clear - Ba Ba1. lia.
- apply (mok_station MT (dxS cx) S1 _ spent _ MTL HMok Bl); [exact LC0|].
  clear - Bc C2 C3 F0. lia.
- (* the footprint: an entry block of drain's own footprint, or a block the walk allocated *)
  unfold lp_FP. destruct (Z.eqb_spec (hl_cap (hs_expected h1)) 0) as [Ec|Ec];
    intros a Ha; [exfalso; exact (inFP_nil a Ha)|].
  destruct Ha as (r & Hr & Hra). cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Hra.
  destruct Hvdisj as [(Hc0 & _) | (_ & Hinv & _)]; [exfalso; exact (Ec Hc0)|].
  pose proof (req_size_pos (AREC * hl_cap (hs_expected h1)) ltac:(clear - HC0; unfold AREC; lia)) as (_ & Hrq).
  assert (HinS : In (hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1)) (asrc_blks h1)).
  { unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. unfold alist_blks.
    rewrite (proj2 (Z.eqb_neq (hl_cap (hs_expected h1)) 0) Ec). apply in_or_app. left. left. reflexivity. }
  destruct (in_dec df_pair_dec (hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))
    (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnin0].
  + left. split;
      [|exists (hl_v (hs_expected h1)), (AREC * hl_cap (hs_expected h1)); split; [exact Hinv | clear - Hra Hrq; lia]].
    pose proof (df_pu_ne_in ly1 S1 W m md (dxG cx, ATABLE) _ _ HAR1 Hperm
      (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl HinS))))) as HNE.
    cbn [fst] in HNE.
    assert (ND : List.NoDup (map fst (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx))).
    { apply (df_pu_nd ly1 S1 W m md _ ((dxG cx, ATABLE) :: aentry_blks e1) [] HAR1).
      rewrite app_nil_r. exact Hperm. }
    pose proof (df_nd_fst _ _ _ ND HinS) as NR.
    pose proof (Permutation_in _ HPerm0 Hin0) as Hin1.
    assert (HinF : In (hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))
      (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx))).
    { destruct Hin1 as [Eq|Hin1]; [injection Eq as E1 E2; exfalso; exact (HNE E1)|].
      apply in_app_or in Hin1 as [Q|Hin1]; [apply in_or_app; left; exact Q|].
      apply in_app_or in Hin1 as [Q|Hin1]; [apply in_or_app; right; apply in_or_app; left; exact Q|].
      apply in_app_or in Hin1 as [Q|Q]; [apply in_or_app; right; apply in_or_app; right; exact Q|].
      exfalso. apply NR. apply in_or_app. right. exact Q. }
    exists (hl_v (hs_expected h1), hl_v (hs_expected h1) + req_size (AREC * hl_cap (hs_expected h1))).
    split; [|cbn [fst snd]; clear - Hra Hrq; lia].
    unfold dFP, dr_fp. right. unfold ablocks_fp.
    exact (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ _ HinF).
  + right. exists (hl_v (hs_expected h1)), (AREC * hl_cap (hs_expected h1)).
    split; [exact Hinv|]. split; [exact Hnin0|]. clear - Hra Hrq; lia.
Qed.

(* ---- df_lp_call's helpers: W_source_reset.v's call kit (azs_sub :92, gx_keep_* :291-342, aj_gx_call :442,
   gx_pres :675, blk_writable :683) and W_lp_tail.v:393 lpt_writable_img, here over G_DR. ---- *)
Lemma df_G1_in : forall x a, inG [(x, 16)] a <-> x <= a < x + 16.
Proof.
intros x a. unfold inG. rewrite Exists_cons, Exists_nil. unfold in_zr. cbn [fst snd].
split; [intros [H | []]; exact H | intros H; left; exact H].
Qed.

Lemma df_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof. intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|]. repeat split; lia. Qed.

Lemma df_lp_rq_out : forall ly S (W : world SEGS) m md p n q k x,
AR SEGS B ly S W m md -> In (p, n) (ablocks B ly S) -> In (q, k) (ablocks B ly S) -> p <> q ->
p <= x < p + req_size n -> ~ (q <= x < q + req_size k).
Proof.
intros ly S W m md p n q k x HAR Hp Hq Hne Hx Hy.
pose proof (df_pw_blocks ly S W m md HAR) as Hpw.
assert (Hne2 : (p, n) <> (q, k)) by (intros E; injection E as E1 _; exact (Hne E1)).
destruct (in_split_2 (p, n) (q, k) _ Hp Hq Hne2) as (l1 & l2 & l3 & [E|E]);
  pose proof (pairwise_In2 _ _ _ _ l1 l2 l3 Hpw E) as D; unfold zdisjoint, block_rng in D; cbn [fst snd] in D;
  revert Hx Hy D; clear; intros; lia.
Qed.

(* list_push's footprint (its vector, when it has one) is a heap block: positive, and apart from every other
   live block *)
Lemma df_lpfp_pos : forall ly S (W : world SEGS) m md LA (l : hlist) lines,
AR SEGS B ly S W m md -> alist_at B ly S W m LA l lines -> ~ YI16.sink_open_fp (lp_FP l).
Proof.
intros ly S W m md LA l lines HAR HL.
pose proof HL as (_ & _ & _ & _ & _ & Hvec & _).
apply sink_closed_pos. unfold lp_FP.
destruct (Z.eqb_spec (hl_cap l) 0) as [Hc | Hc]; [constructor|].
destruct Hvec as [[Hc0 _] | (_ & Hv & _)]; [exfalso; exact (Hc Hc0)|].
destruct (al_blocks _ _ LAWS ly S W m md _ _ HAR Hv) as (_ & H4096 & _).
constructor; [cbn [fst]; clear - H4096; lia | constructor].
Qed.

Lemma df_lpfp_out : forall ly S (W : world SEGS) m md LA (l : hlist) lines p n,
AR SEGS B ly S W m md -> alist_at B ly S W m LA l lines -> In (p, n) (ablocks B ly S) -> p <> hl_v l ->
forall i, 0 <= i < req_size n -> ~ inFP (lp_FP l) (p + i).
Proof.
intros ly S W m md LA l lines p n HAR HL Hin Hne i Hi.
pose proof HL as (_ & _ & _ & _ & _ & Hvec & _).
unfold lp_FP. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc | Hc]; [intros (r & [] & _)|].
destruct Hvec as [[Hc0 _] | (_ & Hv & _)]; [exfalso; exact (Hc Hc0)|].
intros (r & [<- | []] & Hr). cbn [fst snd] in Hr.
destruct (al_blocks _ _ LAWS ly S W m md _ _ HAR Hv) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos _ (proj1 Hn)) as (_ & Rn).
apply (df_lp_rq_out ly S W m md p n (hl_v l) (AREC * hl_cap l) (p + i) HAR Hin Hv Hne ltac:(clear - Hi; lia)).
clear - Hr Rn. lia.
Qed.

(* a callee's journal at G1 inside drain's G_DR: the bytes it keeps *)
Lemma df_keep_hi : forall G1 STK1 sp1 FP1 lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1,
(forall a, inG G1 a -> inG (G_DR B RG) a) ->
ajournal_gx SEGS B G1 0 [] STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 Hsub HJ a Ha Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
rewrite (F1 a Ha Hno). apply (aview_gagree SEGS G1 (w_H W) memc memS a Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by (clear - Ha C1; lia).
intros Hc. pose proof (pa_segs_low a (proj1 (HG a (Hsub a Hc)))) as Hlo.
clear - Hlo Ha C1 C5. lia.
Qed.

Lemma df_keep_img : forall G1 STK1 sp1 FP1 lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1,
~ YI16.sink_open_fp FP1 ->
ajournal_gx SEGS B G1 0 [] STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ inG G1 a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 Hfp HJ a Hi Ho He Hna.
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof (pa_segs_low a Hi) as Hlo.
rewrite (F3 a Hi Ho He ltac:(intros Hso; exfalso; exact (Hfp Hso))).
apply (aview_gagree SEGS G1 (w_H W) memc memS a Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by (unfold kLowMemEnd in Hlo; clear - Hlo; lia).
exact Hna.
Qed.

Lemma df_keep_blk : forall G1 STK1 sp1 FP1 lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 p n,
(forall a, inG G1 a -> inG (G_DR B RG) a) ->
AR SEGS B lyc Sc W memc mdc ->
ajournal_gx SEGS B G1 0 [] STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
In (p, n) (ablocks B lyc Sc) -> (forall i, 0 <= i < req_size n -> ~ inFP FP1 (p + i)) ->
In (p, n) (ablocks B ly2 S2) /\
(forall i, 0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) memc (p + i)).
Proof.
intros G1 STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 p n Hsub HAR HJ Hin Hno.
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc p n HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hn0).
pose proof (req_size_pos n (proj1 Hn0)) as (Hrq & _).
pose proof HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _ & _ & Hgone & _).
assert (Hin2 : In (p, n) (ablocks B ly2 S2)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B ly2 S2)) as [Hc|Hc];
  [exact Hc | exfalso; exact (Hno 0 ltac:(clear - Hrq; lia) (Hgone p n 0 Hin Hc ltac:(clear - Hrq; lia)))]. }
split; [exact Hin2|]. intros i Hi.
rewrite (F2 p n i Hin Hin2 Hi (Hno i Hi)).
apply (aview_gagree SEGS G1 (w_H W) memc memS (p + i) Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by (clear - H4096 Hceil Hi ACL; lia).
intros Hc.
destruct (al_client_img _ _ LAWS lyc Sc W memc mdc (p + i) HAR
  ltac:(left; exists p, n; split; [exact Hin | clear - Hi; lia])) as [_ Hni].
exact (Hni (proj1 (HG (p + i) (Hsub (p + i) Hc)))).
Qed.

(* the call, journal to journal (W_source_reset.v:442 aj_gx_call at G := G_DR) *)
Lemma df_gx_call : forall (G1 : list (Z * Z)) (W : world SEGS) regsT memT pc STK sp0 FP ly S W0 mem md lyc Sc mdc k
STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Z -> Prop),
(forall a, inG G1 a -> inG (G_DR B RG) a) ->
ajournal_gx SEGS B (G_DR B RG) 0 [] STK sp0 FP ly S W0 mem md [] lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memT) (sp0 + o) (s0Z regsT) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsT memT mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx SEGS B G1 0 [] STK1 (sp0 + o) FP1 lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 k1 /\
  aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2 k1)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx SEGS B (G_DR B RG) 0 [] STK sp0 FP ly S W0 mem md [] ly2 S2 W2 mem2 md2 (k + k1) /\
 ajournal_gx SEGS B G1 0 [] STK1 (sp0 + o) FP1 lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 k1 /\
 aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2 k1).
Proof.
intros G1 W regsT memT pc STK sp0 FP ly S W0 mem md lyc Sc mdc k STK1 FP1 o raw ch1 K
HGsub HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
eapply SRr_mono.
{ apply Hcallee. exact (afn_pre_at SEGS B STK sp0 FP ly S W0 memS md [] lyc Sc W memT mdc k regsT STK1 o ch1 HJi
    Hsp Hal Hneg Hstk1 Hbud ltac:(rewrite Hra; exact Hraw) ltac:(unfold raZ; rewrite Hra; exact Hra4) Hgp Htp
    ltac:(rewrite Hsp; exact Hch)). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2, k1. split; [reflexivity|].
split; [|split; [exact HJ1 | split; [exact HP | exact HK]]].
replace (@nil (Z * Z)) with ([] ++ @nil (Z * Z)) by reflexivity.
eapply (ajournal_gx_sub SEGS B LAWS Hsegs (G_DR B RG) STK sp0 0 [] FP ly S W0 mem md [] lyc Sc W memT mdc k
  STK1 (sp0 + o) 0 [] FP1 [] ly2 S2 W2 mem2 md2 k1 HJ);
[ exact (ajournal_gx_G_mono SEGS B G1 (G_DR B RG) 0 [] STK1 (sp0 + o) FP1 lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 k1
    HGsub HJ1)
| clear - Hneg Hbud; lia | clear - Hneg; lia | clear - Hneg; lia | intros a (r & [] & _) | exact HG | exact HF ].
Qed.

Lemma df_gx_pres : forall G0 STK sp0 FP ly S (W0 : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k,
ajournal_gx SEGS B G0 0 [] STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros G0 STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k HJ a Ha.
destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact (Hp a Ha).
Qed.

Lemma df_blk_wr : forall ly S (W : world SEGS) mem md b n,
AR SEGS B ly S W mem md -> In (b, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n ->
writable_at SEGS (mrestrict (w_H W) mem) (b + i).
Proof.
intros ly S W mem md b n HAR Hin i Hi. apply (apresent_writable SEGS).
destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hin) as (_ & _ & _ & _ & Hpr & _).
exact (proj1 (Hpr (b + i) ltac:(clear - Hi; lia))).
Qed.

Lemma df_wr_img : forall (Wa Wb : world SEGS) (m m' : word -> option byte) a,
in_img SEGS a -> (apresent (w_H Wa) m a -> apresent (w_H Wb) m' a) ->
writable_at SEGS (mrestrict (w_H Wa) m) a -> writable_at SEGS (mrestrict (w_H Wb) m') a.
Proof.
intros Wa Wb m m' a Hi Hp Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a)
  by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi) as Hl; unfold kLowMemEnd in Hl; clear - Hl; lia).
assert (HA : w_H Wa (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (HB : w_H Wb (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
unfold writable_at, wview, mrestrict in Hw |- *. rewrite HA in Hw. rewrite HB.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj HA (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* errno: an image byte of a writable segment (HROMO keeps it out of the ROM), so a byte whose view is kept stays
   writable whatever its presence: an absent byte reads through to its segment, which is writable *)
Lemma df_find_seg : forall segs a n seg, find_segment segs a n = Some seg ->
In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
induction segs as [|s segs IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
- injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  split; [left; reflexivity|]. clear - E1 E2. lia.
- destruct (IH a n seg H) as (Hi & H1 & H2). split; [right; exact Hi|]. clear - H1 H2. lia.
Qed.

Lemma df_err_wr : forall (W W2 : world SEGS) m m2 a,
in_img SEGS a -> ~ in_rom SEGS a ->
aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W2) m2) a.
Proof.
intros W W2 m m2 a Hi Hr Hv Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a)
  by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi) as Hl; unfold kLowMemEnd in Hl; clear - Hl; lia).
assert (HA : w_H W (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (HB : w_H W2 (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
apply (mbyte_of_aview SEGS) in Hv.
unfold mbyte, mrestrict in Hv. unfold writable_at, wview, mrestrict in Hw |- *.
rewrite HA in Hv, Hw. rewrite HB in Hv |- *.
destruct (m2 (Z_to_bv 64 a)) as [b2|] eqn:E2; [discriminate|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:E1; [|exact Hw].
clear Hw. cbv beta iota in Hv |- *. rewrite Ha.
destruct (find_segment SEGS a 1) as [seg|] eqn:Fs.
- destruct (seg_writable seg) eqn:Wr.
  + revert Hv. unfold YK11.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite Ha, Fs.
    destruct (seg_readable seg); cbv beta iota zeta; [|intros Hc; discriminate Hc].
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg)))) as [c|];
      [intros _; discriminate | intros Hc; cbv beta iota in Hc; discriminate Hc].
  + exfalso. apply Hr. destruct (df_find_seg SEGS a 1 seg Fs) as (Hin & H1 & H2).
    exists seg. split; [exact Hin|]. split; [exact Wr|]. clear - H1 H2. lia.
- revert Hv. unfold YK11.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite Ha, Fs.
  cbv beta iota. intros Hc; discriminate Hc.
Qed.

(* df_lp_call: the call itself, through LPSPEC at G = [(&h->expected, 16)], composed into drain's journal
   (W_source_reset.v aj_gx_call's shape); the continuation gets the call's effect on memory as the
   keep facts df_close_push takes. *)
Lemma df_lp_call : forall cx ly1 S1 k1 W mc mdc regsc raw (l : hlist) (x : list byte) q qn Q,
DBASE B MT MMAX RG cx ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 W mc mdc k1 ->
spZ regsc = dsp0 cx - DRAIN_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> s0Z regsc < alloc_ceiling ->
getr regsc 10 = w64 (dHA RG cx + 64) -> getr regsc 11 = w64 q -> getr regsc 12 = w64 (Z.of_nat (length x)) ->
alist_at B ly1 S1 W mc (dHA RG cx + 64) l true ->
In (q, qn) (ablocks B ly1 S1) -> q <> hl_v l -> q + Z.of_nat (length x) <= q + req_size qn ->
garr8 SEGS (mrestrict (w_H W) mc) q (bzs x) ->
~ In (Z_to_bv 8 0) x -> Z.of_nat (length x) <= APARTIAL ->
(lp_grow l = true -> lp_vbytes l < MMAX) ->
blocks_bytes S1 + tr_peak (lp_tr l (Z.of_nat (length x))) <= LIVE_MAX ->
mo_ok MT S1 (lp_cost MT l (Z.of_nat (length x))) ->
(forall a, inFP (lp_FP l) a ->
  (inFP (dFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a) ->
(forall W2 ly2 S2 kk regs2 m2 md2 (l2 : hlist) d,
  ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
    (dxmd cx) [] ly2 S2 W2 m2 md2 kk ->
  aregs_preserved regsc regs2 ->
  (forall p n i, In (p, n) (ablocks B ly1 S1) -> p <> hl_v l -> 0 <= i < req_size n ->
     abyte_kept W mc W2 m2 (p + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (dHA RG cx + 64 <= a < dHA RG cx + 80) -> abyte_kept W mc W2 m2 a) ->
  (forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mc W2 m2 a) ->
  (forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W mc W2 m2 a) ->
  rom_view SEGS W2 m2 -> apres_kept B W mc W2 m2 -> frames S2 = frames S1 ->
  alist_at B ly2 S2 W2 m2 (dHA RG cx + 64) l2 true ->
  hl_recs l2 = hl_recs l ++ [(d, x)] ->
  hl_cap l2 = ListRep.grow_cap (hl_n l) (hl_cap l) ->
  (lp_grow l = false -> hl_v l2 = hl_v l) ->
  (forall rest,
   Permutation (ablocks B ly1 S1)
     ((if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []) ++ rest) ->
   Permutation (ablocks B ly2 S2)
     ((d, Z.of_nat (length x) + 1) :: (if lp_grow l then [(hl_v l2, AREC * hl_cap l2)] else []) ++ rest)) ->
  mo_le MT S1 S2 (lp_cost MT l (Z.of_nat (length x))) ->
  SRr SEGS W2 (mkCfg (mkst regs2 raw m2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_list_push)) mc (seg_rom SEGS)) mdc) Q.
Proof.
intros cx ly1 S1 k1 W mc mdc regsc raw l x q qn Q HB HJ Hsp Hgp Htp Hra Hraw Hra4 Hs0 H10 H11 H12 HL Hq Hqv Hqr
  Hsrc Hnz Hlen Hgrow Hbb Hmo HFP HK.
pose proof HB as ((_ & _ & _ & _ & _ & Hstk0 & _) & _ & _ & _ & _ & _ & _ & _ & Hj & _ & _ & _ & _ & _ & _ & Hrv0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HspR : alloc_ceiling + DRAIN_STK <= dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hceil Hslo Hshi H47; lia).
clear Hstk0 Hceil Hslo Hshi H47.
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; clear - Hj; lia).
(* the callee's G: h->expected, 16 bytes of g_s[j] *)
assert (Hsub : forall a, inG [(dHA RG cx + 64, 16)] a -> inG (G_DR B RG) a).
{ intros a Ha. apply (proj1 (df_G1_in _ a)) in Ha.
  exact (proj1 (df_pu_gs a ltac:(clear - Ha HAr; unfold ASRC in *; lia))). }
assert (HG1 : gx_ok SEGS B [(dHA RG cx + 64, 16)]) by exact (gx_ok_sub SEGS B _ _ Hsub HG).
assert (HR1 : gx_rt B [(dHA RG cx + 64, 16)]).
{ intros a Ha. apply (proj1 (df_G1_in _ a)) in Ha.
  pose proof (df_pu_zpw _ 0%nat 2%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D0.
  pose proof (df_pu_zpw _ 1%nat 2%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D1.
  pose proof (df_pu_zpw _ 2%nat 11%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D2.
  cbn [nth] in D0, D1, D2. unfold zdisj in D0, D1, D2. cbn [fst snd] in D0, D1, D2.
  clear - D0 D1 D2 Ha HAr. unfold ASRC in *. repeat split; lia. }
assert (HZ1 : azs B (dHA RG cx + 64) 16).
{ apply (df_azs_sub (rg_s RG) (4 * ASRC));
  [exact HGSZ | clear - HAr; unfold ASRC in *; lia | clear - HAr; unfold ASRC in *; lia]. }
assert (Hx16 : Z.of_nat (length x) < 2 ^ 16) by (unfold APARTIAL in Hlen; clear - Hlen; lia).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
pose proof (df_lpfp_pos ly1 S1 W mc mdc (dHA RG cx + 64) l true HARc HL) as HFPc.
assert (C16 : (- DRAIN_FRAME) mod 16 = 0) by reflexivity.
assert (Cneg : - DRAIN_FRAME <= 0) by (apply Z.leb_le; reflexivity).
assert (CLP : 0 <= LP_STK) by (apply Z.leb_le; reflexivity).
assert (CBUD : LP_STK - - DRAIN_FRAME <= DRAIN_STK) by (apply Z.leb_le; reflexivity).
(* the call: LPSPEC at G1, composed into drain's journal *)
eapply SRr_bind.
{ eapply (df_gx_call [(dHA RG cx + 64, 16)] W regsc mc (BASE + AF_fr_list_push) DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) ly1 S1 mdc k1 LP_STK (lp_FP l) (- DRAIN_FRAME) raw []
    (fun ly2 S2 W2 regs2 mem2 md2 kk => exists (l2 : hlist) (d : Z),
       alist_at B ly2 S2 W2 mem2 (dHA RG cx + 64) l2 true /\
       hl_recs l2 = hl_recs l ++ [(d, x)] /\ hl_cap l2 = ListRep.grow_cap (hl_n l) (hl_cap l) /\
       (lp_grow l = false -> hl_v l2 = hl_v l) /\
       (forall rest,
        Permutation (ablocks B ly1 S1)
          ((if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []) ++ rest) ->
        Permutation (ablocks B ly2 S2)
          ((d, Z.of_nat (length x) + 1) :: (if lp_grow l then [(hl_v l2, AREC * hl_cap l2)] else []) ++ rest)) /\
       apres_kept B W mc W2 mem2 /\
       (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) mc (as_errno B + i)) /\
       frames S2 = frames S1 /\ mo_le MT S1 S2 (lp_cost MT l (Z.of_nat (length x))))
    Hsub HJ Hsp C16 Cneg CLP CBUD Hgp Htp Hra Hraw Hra4 (achain_low _ _ _ _ Hs0)).
  - intros HPRE1. eapply SRr_mono.
    { assert (HLA8 : (dHA RG cx + 64) mod 8 = 0).
      { unfold dHA, ASRC. destruct HGSB as (_ & _ & HG8). clear - HG8.
        apply Z.mod_divide in HG8; [|lia]. destruct HG8 as [k8 Hk8].
        apply Z.mod_divide; [lia|]. exists (k8 + 12 * Z.of_nat (dxj cx) + 8). lia. }
      exact (LPSPEC [(dHA RG cx + 64, 16)] HG1 HR1 W ly1 S1 regsc mc mdc [] (dHA RG cx + 64) q l true x q qn HPRE1
        H10 H11 H12 HLA8 HL (fun a Ha => proj2 (df_G1_in _ a) Ha) HZ1 Hgrow Hx16 Hbb Hq Hqv (Z.le_refl q) Hqr Hsrc
        (fun _ => conj Hnz Hlen) ltac:(intros E; discriminate E) Hmo). }
    cbv beta. unfold lp_post.
    intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & kk & l2 & d & -> & HJ2 & HP2 & HAL & Hrecs & Hcap & Hgv & HPerm &
      HPK & Herr & HFr & HMLE).
    exists ly2, S2, regs2, mem2, md2, kk.
    split; [rewrite Hra; reflexivity|]. split; [rewrite Hsp in HJ2; exact HJ2|]. split; [exact HP2|].
    exists l2, d. split; [exact HAL|]. split; [exact Hrecs|]. split; [exact Hcap|]. split; [exact Hgv|].
    split; [exact HPerm|]. split; [exact HPK|]. split; [exact Herr|]. split; [exact HFr | exact HMLE].
  - exact HFP. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & kk & -> & HJa & HJb & HP &
  (l2 & d & HAL & Hrecs & Hcap & Hgv & HPerm & HPK & Herr & HFr & HMLE)).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJb) as HAR2.
apply (HK W2 ly2 S2 (k1 + kk) regs2 mem2 md2 l2 d).
- exact HJa.
- exact HP.
- (* a live block other than the vector: outside lp_FP l, so the callee's block clause keeps it, and alive *)
  intros p n i Hin Hne Hi.
  destruct (df_keep_blk [(dHA RG cx + 64, 16)] LP_STK (dsp0 cx + - DRAIN_FRAME) (lp_FP l) ly1 S1 W mc mdc
    ly2 S2 W2 mem2 md2 kk p n Hsub HARc HJb Hin
    (df_lpfp_out ly1 S1 W mc mdc (dHA RG cx + 64) l true p n HARc HL Hin Hne)) as [Hin2 Hv].
  split; [exact (Hv i Hi) | intros _; exact (df_blk_wr ly2 S2 W2 mem2 md2 p n HAR2 Hin2 i Hi)].
- (* an image byte off h->expected: the callee's image clause, its presence by apres_kept *)
  intros a Hi Ho He Hn. split.
  + apply (df_keep_img [(dHA RG cx + 64, 16)] LP_STK (dsp0 cx + - DRAIN_FRAME) (lp_FP l) ly1 S1 W mc mdc
      ly2 S2 W2 mem2 md2 kk HFPc HJb a Hi Ho He).
    intros Hc. apply Hn. apply (proj1 (df_G1_in _ a)) in Hc. clear - Hc. lia.
  + exact (df_wr_img W W2 mc mem2 a Hi (HPK a Hi Ho He)).
- (* errno: lp_post's view, and a writable segment's byte *)
  intros a Ha.
  assert (Hv : aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mc a).
  { replace a with (as_errno B + (a - as_errno B)) by ring. apply Herr. clear - Ha. lia. }
  assert (HeG : inG (G_DR B RG) a).
  { unfold G_DR, G_SL, inG. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    clear - Ha. lia. }
  split; [exact Hv|]. intros Hw.
  apply (df_err_wr W W2 mc mem2 a (proj1 (HG a HeG))); [|exact Hv|exact Hw].
  intros Hr. exact (proj1 (proj2 (proj2 (HROMO a Hr))) Ha).
- (* drain's frame: above the callee's window, kept by its stack clause; present by drain's journal *)
  intros a Ha. split.
  + apply (df_keep_hi [(dHA RG cx + 64, 16)] LP_STK (dsp0 cx + - DRAIN_FRAME) (lp_FP l) ly1 S1 W mc mdc
      ly2 S2 W2 mem2 md2 kk Hsub HJb a).
    * clear - HspR Ha. unfold DRAIN_STK, SL_STK, SL_FRAME, ASTACK, DRAIN_FRAME in *. lia.
    * clear - Ha. lia.
  + intros _. apply (apresent_writable SEGS).
    apply (df_gx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJa).
    clear - Ha. unfold DRAIN_STK, SL_STK, SL_FRAME, ASTACK, DRAIN_FRAME in *. lia.
- exact (ajournal_gx_rom_view SEGS B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJa HROMO Hrv0).
- exact HPK.
- exact HFr.
- exact HAL.
- exact Hrecs.
- exact Hcap.
- exact Hgv.
- exact HPerm.
- exact HMLE.
Qed.

(* ---- What the ordinary arm adds to the symbolic state: atom 36 = &h->partial[h->npartial], the alias that
   makes the engine's partial + npartial that atom, its region (the one byte the arm stores) and its shadow
   entry. ---- *)
Definition df_r36 : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 1 [].
Definition df_Pa (HA pn a : Z) : Prop := df_Pg HA a \/ a = pn.

Lemma df_alias36 : forall Ex p n, ew Ex 32 = Z_to_bv 64 p -> ew Ex 33 = Z_to_bv 64 n ->
ew Ex 36 = Z_to_bv 64 (p + n) -> 0 <= p < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= p + n < 2 ^ 64 ->
sv_denot Ex (SAlu ALU_ADD (SOff 32 0) (SOff 33 0)) = sv_denot Ex (SOff 36 0).
Proof.
intros Ex p n H32 H33 H36 Hp Hn Hpn. apply bv_eq.
change (bv_unsigned (sv_denot Ex (SAlu ALU_ADD (SOff 32 0) (SOff 33 0))))
  with (U Ex (SAlu ALU_ADD (SOff 32 0) (SOff 33 0))).
change (bv_unsigned (sv_denot Ex (SOff 36 0))) with (U Ex (SOff 36 0)).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom Ex 32 p H32 Hp), (U_atom Ex 33 n H33 Hn), (U_atom Ex 36 (p + n) H36 Hpn).
apply zcanon_id. unfold M64. lia.
Qed.

Lemma df_denc : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv. cbn. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma df_meq_weak : forall (H : word -> bool) m mc (P P2 : Z -> Prop),
(forall a, P a -> P2 a) -> (forall x : word, ~ P (bv_unsigned x) -> mrestrict H mc x = mrestrict H m x) ->
forall x : word, ~ P2 (bv_unsigned x) -> mrestrict H mc x = mrestrict H m x.
Proof. intros H m mc P P2 HP HM x Hx. apply HM. intros Hp. exact (Hx (HP _ Hp)). Qed.

Lemma df_blk_out_rq : forall ly S (W : world SEGS) m md p n q k x,
AR SEGS B ly S W m md -> In (p, n) (ablocks B ly S) -> In (q, k) (ablocks B ly S) -> p <> q ->
p <= x < p + req_size n -> ~ (q <= x < q + req_size k).
Proof.
intros ly S W m md p n q k x HAR Hp Hq Hne Hx Hy.
pose proof (df_pw_blocks ly S W m md HAR) as Hpw.
assert (Hne2 : (p, n) <> (q, k)) by (intros E; injection E as E1 _; exact (Hne E1)).
destruct (in_split_2 (p, n) (q, k) _ Hp Hq Hne2) as (l1 & l2 & l3 & [E|E]);
  pose proof (pairwise_In2 _ _ _ _ l1 l2 l3 Hpw E) as D; unfold zdisjoint, block_rng in D; cbn [fst snd] in D;
  revert Hx Hy D; clear; intros; lia.
Qed.

(* the frame lies at or above the allocator's ceiling (the journal's stack facts, as df_entry_full reads them) *)
Lemma df_cutjh_sp : forall cx s1 D k p0 ly1 S1 k1 W m md e1 h1 regs,
df_regs cx s1 p0 k regs -> df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 -> alloc_ceiling <= spZ regs <= 2 ^ 47.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md e1 h1 regs HR HC.
pose proof HR as (R2 & _).
destruct HC as (out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 & _ & _ & _ & _ & _ & HMEM & _).
pose proof HMEM as (HJ & _).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK = 16848) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
rewrite R2. lia.
Qed.

Lemma df_body : forall cx s1 D k p0 ly1 S1 k1 W regs m md e1 h1 b Q,
DBASE B MT MMAX RG cx -> df_regs cx s1 p0 k regs -> Z.of_nat k < dnum s1 ->
df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
(forall W2 c2, DRB B MT MMAX RG cx s1 D (S k) W2 c2 -> SRr SEGS W2 c2 Q) ->
(forall W2 c2, DE B MT MMAX RG cx s1 D W2 c2 -> SRr SEGS W2 c2 Q) ->
SRr SEGS W (cfg_at SEGS (BASE + A_dr_feed) regs m md) Q.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W regs m md e1 h1 b Q HB HR Hk HC Hb Hnext Hend.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof HGSB as (HGlo & HGhi & HGal).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
pose proof HR as (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22).
destruct (df_src_byte cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b HC Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & Hb8).
pose proof (df_cutjh_src cx s1 D k p0 ly1 S1 k1 W m md e1 h1 HC) as Hsrc.
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Anp & Aovl & Apb & Apj & Apg & AnoW & _).
assert (Rb : 0 <= b < 2 ^ 64) by lia.
assert (Rov : 0 <= hs_overlong h1 < 2 ^ 64) by (destruct Aovl as [-> | ->]; lia).
assert (Rnp : 0 <= hs_npartial h1 < 2 ^ 64) by (unfold APARTIAL in Anp; lia).
destruct (df_entry_full cx s1 D k p0 ly1 S1 k1 W regs m md e1 h1 b HB HR Hk HC Hb) as (HS & SHOK).
pose proof (df_cutjh_journal cx s1 D k p0 ly1 S1 k1 W m md e1 h1 HC) as HJ.
remember (Eimg (Ereg regs (df_extra (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn'. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn'. }
assert (E33 : ew E 33 = Z_to_bv 64 (hs_npartial h1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hs_overlong h1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 b)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E32 : ew E 32 = Z_to_bv 64 (hs_partial h1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E36 : ew E 36 = Z_to_bv 64 (hs_partial h1 + hs_npartial h1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (HAe : dHA RG cx = rg_s RG + ASRC * Z.of_nat (dxj cx)) by reflexivity.
assert (U23 : bv_unsigned (ew E 23) = dHA RG cx).
{ rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64. apply unsigned_lit_small. rewrite HAe. unfold ASRC in *. lia. }
assert (E23 : ew E 23 = Z_to_bv 64 (dHA RG cx)) by (rewrite (EE 23%nat 23%bv eq_refl), R23; reflexivity).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl), R21; reflexivity).
assert (HAr : 0x10000 <= dHA RG cx /\ dHA RG cx + 96 <= 0x5fb000)
  by (rewrite HAe; unfold ASRC in *; clear - HGlo HGhi Hj; lia).
clear HE.
assert (MEQ : forall x : word, ~ df_Pg (dHA RG cx) (bv_unsigned x) -> mrestrict (w_H W) m x = mrestrict (w_H W) m x)
  by (intros; reflexivity).
assert (PR : forall a, apresent (w_H W) m a -> apresent (w_H W) m a) by (intros a Ha; exact Ha).
unfold cfg_at.
paj_run_tok RUN HS HJ SHOK DFspan. { df_awr U23 HAe. }
df_track m MEQ PR U23.
psrr_branch_tok RUN BR HS SHOK DFspan.
- (* 0x8349c taken: b = 0 *)
  rewrite branch_eq_U, df_U0 in Hc. df_Uat Hc 35%nat b E35 Rb. apply Z.eqb_eq in Hc. rename Hc into Hb0.
  paj_run_tok RUN HS HJ SHOK DFspan. { df_awr U23 HAe. }
  df_track m MEQ PR U23.
  psrr_branch_tok RUN BR HS SHOK DFspan.
  + (* 0x834d0 taken: overlong <> 0, reset *)
    rewrite branch_ne_U, df_U0 in Hc. df_Uat Hc 34%nat (hs_overlong h1) E34 Rov.
    pose proof (df_ovl_nz _ Aovl Hc) as Hov1. clear Hc.
    df_leaf_run HS HJ SHOK U23 HAe m MEQ PR 1%nat.
    refine (df_finish_nw cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b _ _ _ 0 0 Q HB _ Hk HC Hb HJ
      (df_keep_of_meq W m _ (df_Pg (dHA RG cx)) MEQ PR) PR _ _ _ _ _ _ _ Hnext Hend).
    * df_regs_tac HS HR EE E23 E21 HAr R20 R27 R22.
    * df_v (dHA RG cx) U23 48 8%N (SLit 0) 0; [reflexivity | cbn; lia].
    * df_v (dHA RG cx) U23 56 4%N (SLit 0) 0; [reflexivity | cbn; lia].
    * unfold APARTIAL. lia.
    * left. reflexivity.
    * rewrite Hb0, (df_step_reset h1 Hov1). apply df_state_reset; reflexivity.
    * rewrite Hb0, (df_step_reset h1 Hov1). reflexivity.
    * intros [].
  + (* 0x834d0 fall: overlong = 0, push *)
    rewrite branch_ne_U, df_U0 in Hc. df_Uat Hc 34%nat (hs_overlong h1) E34 Rov.
    pose proof (df_ovl_z _ Hc) as Hov0. clear Hc.
    (* ---- the call list_push (&h->expected, h->partial, h->npartial) at 0x834f0 ---- *)
    subst b.
    pose proof (df_cutjh_journal cx s1 D k p0 ly1 S1 k1 W m md e1 h1 HC) as HJ0.
    assert (HAR0 : AR SEGS B ly1 S1 W m md) by (eapply ajournal_gx_AR; exact HJ0).
    destruct (df_push_pre cx s1 D k p0 ly1 S1 k1 W m md e1 h1 HB HC Hb Hov0)
      as (PAL & PPB & PNE & PG8 & PNZ & PLEN & PGR & PLIVE & PMO & PFP).
    pose proof (df_cutjh_sp cx s1 D k p0 ly1 S1 k1 W m md e1 h1 regs HR HC) as Hsp.
    pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & HrqA).
    pose proof HB as (HPRE0 & _).
    pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
    assert (HAlo : rg_s RG <= dHA RG cx) by (rewrite HAe; unfold ASRC; clear; lia).
    assert (HAhi : dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (rewrite HAe; unfold ASRC in *; clear - Hj; lia).
    paj_run_to_tok RUNTO HS HJ SHOK DFspan AF_fr_list_push. { df_awr U23 HAe. }
    df_track m MEQ PR U23.
    pmkst HS.
    df_reg HS (2%bv : bv 5) Q2. df_reg HS (3%bv : bv 5) Q3. df_reg HS (4%bv : bv 5) Q4. df_reg HS (8%bv : bv 5) Q8.
    df_reg HS (10%bv : bv 5) Q10. df_reg HS (11%bv : bv 5) Q11. df_reg HS (12%bv : bv 5) Q12.
    prreg HS (1%bv : bv 5) T1.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?ms0) _ (ms_mem ?ms0) _; cfg_model := ?md0 |} _ =>
      set (rc0 := ms_regs ms0) in *; set (mc := ms_mem ms0) in *; set (mdc := md0) in * end.
    assert (G2 : getr rc0 2 = getr regs 2)
      by (apply (df_reg_atom _ _ _ _ _ 2%nat Q2); cbn [ew ewset Nat.eqb]; exact (EE 2%nat 2%bv eq_refl)).
    assert (G3 : getr rc0 3 = getr regs 3)
      by (apply (df_reg_atom _ _ _ _ _ 3%nat Q3); cbn [ew ewset Nat.eqb]; exact (EE 3%nat 3%bv eq_refl)).
    assert (G4 : getr rc0 4 = getr regs 4)
      by (apply (df_reg_atom _ _ _ _ _ 4%nat Q4); cbn [ew ewset Nat.eqb]; exact (EE 4%nat 4%bv eq_refl)).
    assert (G8 : getr rc0 8 = getr regs 8)
      by (apply (df_reg_atom _ _ _ _ _ 8%nat Q8); cbn [ew ewset Nat.eqb]; exact (EE 8%nat 8%bv eq_refl)).
    assert (HxL : Z.of_nat (length (hs_W h1)) = hs_npartial h1) by exact (df_hsW_len h1 Anp Apj).
    refine (df_lp_call cx ly1 S1 k1 W mc _ rc0 (getr rc0 1) (hs_expected h1) (hs_W h1) (hs_partial h1) APARTIAL Q
      HB HJ _ _ _ eq_refl _ _ _ _ _ _ _ PPB PNE _ _ PNZ PLEN PGR PLIVE PMO PFP _).
    { unfold spZ in R2 |- *. rewrite G2. exact R2. }
    { rewrite G3, R3. exact Hgp0. }
    { rewrite G4, R4. exact Htp0. }
    { rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { rewrite T1, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_B_ok. lia. }
    { unfold s0Z. rewrite G8, R8. unfold w64. pose proof asan_consts as (C1 & _).
      assert (Hd : 0 <= (rg_s RG + 4) / 8 <= rg_s RG + 4)
        by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; clear - HGlo; lia).
      rewrite unsigned_lit_small by (clear - Hd HGlo HGhi; unfold ASRC in *; lia).
      clear - Hd HGlo HGhi C1. unfold ASRC in *. lia. }
    { rewrite Q10. unfold w64. apply df_denc; [cbn [ew ewset Nat.eqb]; exact E23 | clear - HAr; lia]. }
    { rewrite Q11. unfold w64. apply df_den0. cbn [ew ewset Nat.eqb]. exact E32. }
    { rewrite Q12, HxL. unfold w64. apply df_den0. cbn [ew ewset Nat.eqb]. exact E33. }
    { apply (alist_at_kept B ly1 S1 W m ly1 S1 W mc _ _ _ PAL).
      - apply (df_pu_alist_kept ly1 S1 W W m mc _ _ _ PAL).
        + intros a Ha. apply (df_keep_of_meq W m mc (df_Pg (dHA RG cx)) MEQ PR a);
            [clear - Ha HAr; lia | unfold df_Pg; clear - Ha; lia].
        + intros p n a Hpn Ha.
          destruct (df_heap_np ly1 S1 W m md (dHA RG cx) p n a HAR0
            (df_alist_blks_in ly1 S1 W m _ _ _ PAL (p, n) Hpn) Ha HAlo HAhi) as (F1 & F2).
          exact (df_keep_of_meq W m mc (df_Pg (dHA RG cx)) MEQ PR a F1 F2).
      - intros bb Hbb. exact (df_alist_blks_in ly1 S1 W m _ _ _ PAL bb Hbb). }
    { rewrite HxL. clear - Anp HrqA. unfold APARTIAL in *. lia. }
    { apply (garr8_frame SEGS (mrestrict (w_H W) m) (mrestrict (w_H W) mc) _ _ PG8).
      intros a Ha. apply (mbyte_of_aview SEGS). unfold bzs in Ha. rewrite length_map, HxL in Ha.
      destruct (df_heap_np ly1 S1 W m md (dHA RG cx) (hs_partial h1) APARTIAL a HAR0 PPB
        ltac:(clear - Ha Anp HrqA; unfold APARTIAL in *; lia) HAlo HAhi) as (F1 & F2).
      exact (proj1 (df_keep_of_meq W m mc (df_Pg (dHA RG cx)) MEQ PR a F1 F2)). }
    intros W2 ly2 S2 kk regs2 m2 md2 l2 d HJ2 HAP KB KI KE KF HROM2 HPK2 HFR2 HL2 Hrecs Hcap Hv HPERM HMO.
    (* ---- back at 0x834f4: drain's state after the call ---- *)
    assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
    assert (HDF : DRAIN_FRAME = 336) by reflexivity.
    pose proof asan_consts as (C1 & _).
    rewrite T1.
    jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) m2) HAP [0; 1]%nat HS2.
    match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb];
          rewrite U2; intros a Ha.
        + apply (mbyte_of_aview SEGS). apply (proj1 (KF a ltac:(unfold spZ in *; clear - Ha R2 HDF; lia))).
        + exfalso. clear - Ha. lia.
      - assert (KG : forall a, dHA RG cx + 40 <= a < dHA RG cx + 60 -> abyte_kept W mc W2 m2 a).
        { intros a Ha.
          assert (Hg : rg_s RG <= a < rg_s RG + 4 * ASRC) by (rewrite HAe in Ha; unfold ASRC in *; clear - Ha Hj; lia).
          destruct (df_pu_gs a Hg) as (HgG & Hne).
          destruct (HG a HgG) as (Hi & Ho & _).
          apply (KI a Hi Ho Hne). clear - Ha. lia. }
        split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb];
          rewrite U23; intros a Ha.
        + apply (mbyte_of_aview SEGS). exact (proj1 (KG a Ha)).
        + intros Hw. exact (proj2 (KG a ltac:(clear - Ha; lia)) Hw). }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    lazymatch type of HS with st_ok_pi _ _ (havoc ?Ex 40 ?lc) _ _ =>
      assert (OLDc : forall n, (n < 40)%nat -> ew (havoc Ex 40 lc) n = ew Ex n)
        by (intros n Hn; apply YN3v.ew_havoc_old; exact Hn);
      assert (HEIc : img_env VAL A_LIM (havoc Ex 40 lc)) by (apply img_env_havoc; [assumption | cbv; lia]);
      remember (havoc Ex 40 lc) as Ec eqn:HEc in HS, OLDc, HEIc
    end.
    clear HEc.
    assert (EEc : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ec n = getr regs r).
    { intros n r Hn'. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
      rewrite OLDc by lia. rewrite !ew_ewset_other by lia. exact (EE n r Hn'). }
    assert (E23c : ew Ec 23 = Z_to_bv 64 (dHA RG cx)) by (rewrite (EEc 23%nat 23%bv eq_refl), R23; reflexivity).
    assert (E21c : ew Ec 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEc 21%nat 21%bv eq_refl), R21; reflexivity).
    assert (U23c : bv_unsigned (ew Ec 23) = dHA RG cx) by (rewrite E23c; apply unsigned_lit_small; clear - HAr; lia).
    pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
    assert (SHOKc : sh_ok SEGS df_Bx [mkSHE 23 0 96] Ec (mrestrict (w_H W2) m2)).
    { unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
      eapply shent_ok_of_range.
      - exact (azs_range_addressable B LAWS ly2 S2 W2 m2 md2 (rg_s RG) (4 * ASRC) HAR2 HGSZ).
      - unfold df_Bx. apply U_atom; [exact E21c | unfold SHADOW_OFF; lia].
      - apply U_atom; [exact E23c | clear - HAr; lia].
      - clear - HAlo. lia.
      - clear - HAhi. unfold ASRC in *. lia.
      - intros x Hx. change (Z.min 0 96) with 0 in Hx. change (Z.max 0 96) with 96 in Hx.
        unfold SHADOW_OFF. clear - Hx HAr. lia. }
    clear SHOK.
    assert (MEQc : forall x : word, ~ df_Pg (dHA RG cx) (bv_unsigned x) ->
      mrestrict (w_H W2) m2 x = mrestrict (w_H W2) m2 x) by (intros; reflexivity).
    assert (PRc : forall a, apresent (w_H W2) m2 a -> apresent (w_H W2) m2 a) by (intros a Ha; exact Ha).
    paj_run_to_tok RUNTO HS HJ2 SHOKc DFspan A_df_tail. { df_awr U23c HAe. }
    df_track m2 MEQc PRc U23c.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
    pmkst HS.
    refine (df_tail cx s1 D k p0 W2 _ _ _ Q _ _ _ Hnext Hend).
    * df_regs_tac HS HR EEc E23c E21c HAr R20 R27 R22.
    * exists ly2, S2, kk, e1. eexists.
      refine (df_close_push cx s1 D k p0 ly1 S1 k1 W m md e1 h1 ly2 S2 kk W2 _ _ l2 d HB HC Hb Hov0 HJ2
        _ _ _ _ _ _ HFR2 _ _ _ Hrecs Hcap Hv HPERM HMO).
      -- intros p n i Hin Hne Hi.
        destruct (df_heap_np ly1 S1 W m md (dHA RG cx) p n (p + i) HAR0 Hin ltac:(clear - Hi; lia) HAlo HAhi)
          as (F1 & F2).
        apply (df_bk_trans W W2 W2 m m2 _ (p + i)).
        ++ apply (df_bk_trans W W W2 m mc m2 (p + i)).
           ** exact (df_keep_of_meq W m mc (df_Pg (dHA RG cx)) MEQ PR (p + i) F1 F2).
           ** exact (KB p n i Hin Hne Hi).
        ++ exact (df_keep_of_meq W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc (p + i) F1 F2).
      -- intros a Hi Ho He H48 H64.
        destruct (df_img_np (dHA RG cx) a Hi H48) as (F1 & F2).
        apply (df_bk_trans W W2 W2 m m2 _ a).
        ++ apply (df_bk_trans W W W2 m mc m2 a).
           ** exact (df_keep_of_meq W m mc (df_Pg (dHA RG cx)) MEQ PR a F1 F2).
           ** exact (KI a Hi Ho He H64).
        ++ exact (df_keep_of_meq W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a F1 F2).
      -- intros a Ha.
        assert (Hcase : (0 <= a < 2 ^ 64 /\ ~ (rg_s RG <= a < rg_s RG + 4 * ASRC)) /\
          ((as_errno B <= a < as_errno B + 4) \/
           (in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)))).
        { destruct Ha as [Hc | [Hc | [Hc | He]]].
          - destruct (df_cell_facts a (or_introl Hc)) as (F1 & F2 & F3 & F4 & F5).
            split; [split; assumption | right; split; [exact F3 | split; assumption]].
          - destruct (df_cell_facts a (or_intror (or_introl Hc))) as (F1 & F2 & F3 & F4 & F5).
            split; [split; assumption | right; split; [exact F3 | split; assumption]].
          - destruct (df_cell_facts a (or_intror (or_intror Hc))) as (F1 & F2 & F3 & F4 & F5).
            split; [split; assumption | right; split; [exact F3 | split; assumption]].
          - destruct (df_errno_facts a He) as (F1 & F2 & F3).
            split; [split; assumption | left; exact He]. }
        destruct Hcase as ((F1 & F2) & Hcase).
        assert (F3 : ~ df_Pg (dHA RG cx) a)
          by (unfold df_Pg; rewrite HAe; unfold ASRC in *; clear - F2 Hj; lia).
        apply (df_bk_trans W W2 W2 m m2 _ a).
        ++ apply (df_bk_trans W W W2 m mc m2 a).
           ** exact (df_keep_of_meq W m mc (df_Pg (dHA RG cx)) MEQ PR a F1 F3).
           ** destruct Hcase as [He | (Hi & Ho & He)]; [exact (KE a He)|].
              apply (KI a Hi Ho He). rewrite HAe. unfold ASRC in *. clear - F2 Hj. lia.
        ++ exact (df_keep_of_meq W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a F1 F3).
      -- intros a Ha.
        assert (F1 : 0 <= a < 2 ^ 64) by (unfold spZ in *; clear - Ha Hsp R2 HDF C1; lia).
        assert (F3 : ~ df_Pg (dHA RG cx) a) by (unfold df_Pg, spZ in *; clear - Ha Hsp R2 HDF C1 HAr; lia).
        apply (df_bk_trans W W2 W2 m m2 _ a).
        ++ apply (df_bk_trans W W W2 m mc m2 a).
           ** exact (df_keep_of_meq W m mc (df_Pg (dHA RG cx)) MEQ PR a F1 F3).
           ** exact (KF a Ha).
        ++ exact (df_keep_of_meq W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a F1 F3).
      -- intros a Ha.
        assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
        assert (H48 : ~ (dHA RG cx + 48 <= a < dHA RG cx + 60)).
        { intros Hg. apply (HGR a); [|exact Ha].
          unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
          rewrite HAe in Hg. unfold ASRC in *. clear - Hg Hj. lia. }
        destruct (df_img_np (dHA RG cx) a Hi H48) as (F1 & F2).
        rewrite (proj1 (df_keep_of_meq W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a F1 F2)). exact (HROM2 a Ha).
      -- intros a Hi Ho He Hp. apply PRc. apply (HPK2 a Hi Ho He). apply PR. exact Hp.
      -- apply (alist_at_kept B ly2 S2 W2 m2 ly2 S2 W2 _ _ _ _ HL2).
        ++ apply (df_pu_alist_kept ly2 S2 W2 W2 m2 _ _ _ _ HL2).
           ** intros a Ha. apply (df_keep_of_meq W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a);
                [clear - Ha HAr; lia | unfold df_Pg; clear - Ha; lia].
           ** intros p n a Hpn Ha.
              destruct (df_heap_np ly2 S2 W2 m2 md2 (dHA RG cx) p n a HAR2
                (df_alist_blks_in ly2 S2 W2 m2 _ _ _ HL2 (p, n) Hpn) Ha HAlo HAhi) as (F1 & F2).
              exact (df_keep_of_meq W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a F1 F2).
        ++ intros bb Hbb. exact (df_alist_blks_in ly2 S2 W2 m2 _ _ _ HL2 bb Hbb).
      -- df_v (dHA RG cx) U23c 48 8%N (SLit 0) 0; [reflexivity | cbn; lia].
      -- df_v (dHA RG cx) U23c 56 4%N (SLit 0) 0; [reflexivity | cbn; lia].
    * clear - Hk. lia.
- (* 0x8349c fall: b <> 0 *)
  rewrite branch_eq_U, df_U0 in Hc. df_Uat Hc 35%nat b E35 Rb. apply Z.eqb_neq in Hc. rename Hc into Hb0.
  paj_run_tok RUN HS HJ SHOK DFspan. { df_awr U23 HAe. }
  df_track m MEQ PR U23.
  psrr_branch_tok RUN BR HS SHOK DFspan.
  + (* 0x834a0 taken: overlong <> 0, skip *)
    rewrite branch_ne_U, df_U0 in Hc. df_Uat Hc 34%nat (hs_overlong h1) E34 Rov.
    pose proof (df_ovl_nz _ Aovl Hc) as Hov1. clear Hc.
    df_leaf_run HS HJ SHOK U23 HAe m MEQ PR 1%nat.
    refine (df_finish_nw cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b _ _ _ (hs_npartial h1) (hs_overlong h1) Q HB _ Hk
      HC Hb HJ (df_keep_of_meq W m _ (df_Pg (dHA RG cx)) MEQ PR) PR _ _ _ _ _ _ _ Hnext Hend).
    * df_regs_tac HS HR EE E23 E21 HAr R20 R27 R22.
    * df_v (dHA RG cx) U23 48 8%N (SOff 33 0) (hs_npartial h1);
        [apply df_den0; cbn [ew ewset Nat.eqb]; exact E33 | cbn; clear - Rnp; lia].
    * df_v (dHA RG cx) U23 56 4%N (SOff 34 0) (hs_overlong h1);
        [apply df_den0; cbn [ew ewset Nat.eqb]; exact E34 | cbn; rewrite Hov1; lia].
    * exact Anp.
    * right. exact Hov1.
    * rewrite (df_step_skip h1 b Hb0 Hov1). apply df_state_skip; reflexivity.
    * rewrite (df_step_skip h1 b Hb0 Hov1). reflexivity.
    * exact AnoW.
  + rewrite branch_ne_U, df_U0 in Hc. df_Uat Hc 34%nat (hs_overlong h1) E34 Rov.
    pose proof (df_ovl_z _ Hc) as Hov0. clear Hc.
    paj_run_tok RUN HS HJ SHOK DFspan. { df_awr U23 HAe. }
    df_track m MEQ PR U23.
    psrr_branch_tok RUN BR HS SHOK DFspan.
    * (* 0x834b8 taken: npartial <> 6000, add *)
      rewrite branch_ne_U, df_U6000 in Hc. df_Uat Hc 33%nat (hs_npartial h1) E33 Rnp.
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hnp6.
      assert (HnpA : hs_npartial h1 <> APARTIAL) by (unfold APARTIAL; exact Hnp6).
      assert (Hnp : 0 <= hs_npartial h1 < APARTIAL) by (clear - Anp HnpA; lia).
      pose proof (df_cutjh_journal cx s1 D k p0 ly1 S1 k1 W m md e1 h1 HC) as HJ0.
      assert (HAR0 : AR SEGS B ly1 S1 W m md) by (eapply ajournal_gx_AR; exact HJ0).
      destruct (al_blocks SEGS B LAWS ly1 S1 W m md _ _ HAR0 Apb) as (_ & Hp4096 & Hpceil & Happ & Hppres & _ & _).
      pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & HrqA).
      pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
      pose proof (df_cutjh_sp cx s1 D k p0 ly1 S1 k1 W m md e1 h1 regs HR HC) as Hsp.
      destruct (df_src_byte cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b HC Hb)
        as (q & qn & Hqin & _ & Hqne & Hq1 & Hq2 & _ & _).
      destruct (al_blocks SEGS B LAWS ly1 S1 W m md q qn HAR0 Hqin) as (_ & Hq4096 & Hqceil & _ & _ & _ & _).
      pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSAME & _).
      pose proof HSAME as (_ & _ & _ & _ & _ & _ & _ & Hpsame & _).
      set (pn := hs_partial h1 + hs_npartial h1) in *.
      assert (Hin_pn : hs_partial h1 <= pn < hs_partial h1 + req_size APARTIAL) by (unfold pn; clear - Hnp HrqA; lia).
      assert (Hpn64 : 4096 <= pn /\ pn + 1 <= alloc_ceiling /\ 0 <= pn < 2 ^ 64)
        by (clear - Hin_pn Hp4096 Hpceil ACL; lia).
      assert (Hpngs : pn + 1 <= dHA RG cx + 40 \/ dHA RG cx + 60 <= pn).
      { assert (Hin' : hs_partial h1 <= pn < hs_partial h1 + APARTIAL) by (unfold pn; clear - Hnp; lia).
        pose proof (df_blk_gs ly1 S1 W m md _ _ _ HAR0 Apb Hin') as Hng.
        rewrite HAe. unfold ASRC in *.
        destruct (Z_lt_le_dec pn (rg_s RG)) as [Hlt|Hge]; [left; clear - Hlt; lia|].
        destruct (Z_lt_le_dec pn (rg_s RG + 4 * 96)) as [Hlt2|Hge2]; [exfalso; apply Hng; split; assumption|].
        right. clear - Hge2 Hj. lia. }
      assert (Hpnsrc : pn + 1 <= p0 + Z.of_nat k \/ p0 + Z.of_nat k + 1 <= pn).
      { pose proof (df_blk_out_rq ly1 S1 W m md _ _ q qn _ HAR0 Apb Hqin (not_eq_sym Hqne) Hin_pn) as Hno.
        destruct (Z_lt_le_dec pn (p0 + Z.of_nat k)) as [Hlt|Hge]; [left; clear - Hlt; lia|right].
        destruct (Z.eq_dec pn (p0 + Z.of_nat k)) as [Heq|Hne]; [|clear - Hge Hne; lia].
        exfalso. apply Hno. clear - Heq Hq1 Hq2. lia. }
      assert (U36 : bv_unsigned (ew E 36) = pn) by (rewrite E36; apply unsigned_lit_small; tauto).
      assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
      assert (U26 : bv_unsigned (ew E 26) = p0 + Z.of_nat k).
      { rewrite (EE 26%nat 26%bv eq_refl), R26. unfold w64. apply unsigned_lit_small.
        clear - Hq1 Hq2 Hq4096 Hqceil ACL. pose proof (req_size_pos qn) as Hrq. lia. }
      lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
        assert (AF36 : afact_ok Ex 36 df_HEAPF);
        [ unfold afact_ok, df_HEAPF; cbn [af_lo af_hi af_al2 ew ewset Nat.eqb]; rewrite U36;
          rewrite Z.pow_0_r, Z.mod_1_r; pose proof asan_consts as (C1 & _);
          clear - Hpn64 C1; repeat match goal with |- _ /\ _ => split end; (exact I || lia) |];
        assert (AL36 : sv_denot Ex (SAlu ALU_ADD (SOff 32 0) (SOff 33 0)) = sv_denot Ex (SOff 36 0));
        [ apply (df_alias36 Ex (hs_partial h1) (hs_npartial h1)); cbn [ew ewset Nat.eqb];
          [exact E32 | exact E33 | exact E36 | clear - Hp4096 Hpceil ACL HrqA; unfold APARTIAL in *; lia | exact Rnp | tauto] |]
      end.
      pose proof (st_ok_pi_add_fact _ _ _ 36 df_HEAPF HS AF36) as HS1. clear HS. rename HS1 into HS. norm_ss HS.
      pose proof (st_ok_pi_add_alias _ _ _ _ _ HS AL36) as HS1. clear HS. rename HS1 into HS. norm_ss HS.
      lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
        assert (RG36 : region_ok SEGS Ex (ms_mem (restrict (w_H W) msx)) df_r36);
        [ unfold region_ok, df_r36;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict
            ew ewset Nat.eqb]; rewrite U36;
          split; [clear - Hpn64; lia|]; split; [clear - Hpn64; lia|]; split; [|apply Forall_nil];
          intros o Ho; apply (apresent_writable SEGS); replace (pn + o) with pn by (clear - Ho; lia);
          apply PR; exact (proj1 (Hppres pn Hin_pn)) |];
        assert (DJ36 : all_disjoint Ex df_r36 (ss_mem ssx));
        [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, df_r36;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val ew ewset Nat.eqb]; rewrite U36, U2, U23, U26;
          split; [left; clear - Hsp Hpn64; lia|]; split; [clear - Hpngs; lia|]; split; [clear - Hpnsrc; lia|];
          exact I |]
      end.
      pose proof (st_ok_pi_add_region _ _ _ df_r36 HS eq_refl RG36 DJ36) as HS1. clear HS. rename HS1 into HS.
      norm_ss HS.
      lazymatch type of SHOK with sh_ok _ _ _ ?Ex ?mx =>
        assert (SHOK2 : sh_ok SEGS df_Bx (mkSHE 36 0 1 :: df_SH) Ex mx);
        [ unfold sh_ok; apply Forall_cons; [|exact SHOK];
          eapply (shent_ok_of_range SEGS (w_H W) _ Ex df_Bx 36%nat pn 1 pn 0 1);
          [ eapply (range_addressable_of_block SEGS B LAWS ly1 S1 W _ _ (hs_partial h1) APARTIAL);
            [ exact (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) | exact Apb
            | clear - Hin_pn; lia | clear - Hin_pn; lia ]
          | unfold df_Bx; apply U_atom; [cbn [ew ewset Nat.eqb]; exact E21 | unfold SHADOW_OFF; lia]
          | apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite E36; reflexivity | tauto]
          | lia | lia
          | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia; revert Happ Hin_pn Hx; clear;
            unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; lia ] |]
      end.
      clear SHOK. rename SHOK2 into SHOK.
      pose proof (df_meq_weak (w_H W) m _ (df_Pg (dHA RG cx)) (df_Pa (dHA RG cx) pn) (fun a Ha => or_introl Ha) MEQ)
        as MEQ2.
      clear MEQ.
      paj_run_to_tok RUNTO HS HJ SHOK DFspan A_df_tail.
      { lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?bl0 ?blc ?ly ?own =>
          let rs2 := eval vm_compute in rs in change (awr_ok_x E rs2 G XO OUT STK sp0 FP bl0 blc ly own) end.
        apply awr_ok_x_cons.
        - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Ha. rewrite U36 in Ha.
          left. split; [|clear - Ha; lia].
          unfold awr_byte. right. left. split.
          + exists (hs_partial h1, hs_partial h1 + req_size APARTIAL). split; [|cbn [fst snd]; clear - Ha Hin_pn; lia].
            unfold dFP, dr_fp. right. unfold ablocks_fp.
            apply (in_map (fun b0 => (fst b0, fst b0 + req_size (snd b0))) _ (hs_partial h1, APARTIAL)).
            apply in_or_app. right. apply in_or_app. left. unfold asrc_blks. left. rewrite Hpsame. reflexivity.
          + exists (hs_partial h1), APARTIAL. split; [exact Apb | clear - Ha Hin_pn; lia].
        - df_awr U23 HAe. }
      lazymatch goal with
      | HF : frame_of ?Ex ?rs (mrestrict ?Hh ?mc) (mrestrict ?Hh ?mn),
        HGr : mem_grows (mrestrict ?Hh ?mc) (mrestrict ?Hh ?mn) |- _ =>
        pose proof (df_meq_step Ex rs Hh m mc mn (df_Pa (dHA RG cx) pn) MEQ2 HF
          ltac:(intros a Ha; pose proof (df_wrange Ex rs a ltac:(vm_compute; reflexivity) Ha) as Hw;
                cbn [ew ewset Nat.eqb] in Hw; rewrite U23, U36 in Hw; exact Hw)) as MEQ3;
        assert (PR3 : forall a, apresent Hh m a -> apresent Hh mn a)
          by (intros a Ha; exact (apresent_grows Hh mc mn a HGr (PR a Ha)))
      end.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RGb. cbn [ms_mem restrict] in RGb.
      pmkst HS.
      refine (df_finish_add cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b _ _ _ Q HB _ Hk HC Hb Hb0 Hov0 HnpA HJ
        (fun a Ha H1 H2 => df_keep_of_meq W m _ (df_Pa (dHA RG cx) pn) MEQ3 PR3 a Ha
           (fun H => match H with or_introl H' => H1 H' | or_intror H' => H2 H' end)) PR3 _ _ _ Hnext Hend).
      -- df_regs_tac HS HR EE E23 E21 HAr R20 R27 R22.
      -- df_v (dHA RG cx) U23 48 8%N (SOff 33 1) (hs_npartial h1 + 1);
           [apply df_denc; [cbn [ew ewset Nat.eqb]; exact E33 | exact Rnp] | cbn; clear - Hnp; unfold APARTIAL in *; lia].
      -- df_v (dHA RG cx) U23 56 4%N (SOff 34 0) 0;
           [apply df_den0; cbn [ew ewset Nat.eqb]; rewrite E34, Hov0; reflexivity | cbn; lia].
      -- unfold arm. rewrite <- (Z.add_0_r (hs_partial h1 + hs_npartial h1)).
         eapply (field_of_region _ _ 36%nat pn _ _ _ _ _ 0 1%N (SOff 35 0) b RGb);
           [cbn [ew ewset Nat.eqb]; exact U36 | cbn [In]; df_inc | apply df_den0; cbn [ew ewset Nat.eqb]; exact E35
           | cbn; clear - Hb8; lia | cbn; lia].
    * (* 0x834b8 fall: npartial = 6000, long *)
      rewrite branch_ne_U, df_U6000 in Hc. df_Uat Hc 33%nat (hs_npartial h1) E33 Rnp.
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hnp6.
      assert (HnpA : hs_npartial h1 = APARTIAL) by (unfold APARTIAL; exact Hnp6).
      df_leaf_run HS HJ SHOK U23 HAe m MEQ PR 1%nat.
      refine (df_finish_nw cx s1 D k p0 ly1 S1 k1 W m md e1 h1 b _ _ _ (hs_npartial h1) 1 Q HB _ Hk
        HC Hb HJ (df_keep_of_meq W m _ (df_Pg (dHA RG cx)) MEQ PR) PR _ _ _ _ _ _ _ Hnext Hend).
      -- df_regs_tac HS HR EE E23 E21 HAr R20 R27 R22.
      -- df_v (dHA RG cx) U23 48 8%N (SOff 33 0) (hs_npartial h1);
           [apply df_den0; cbn [ew ewset Nat.eqb]; exact E33 | cbn; clear - Rnp; lia].
      -- df_v (dHA RG cx) U23 56 4%N (SLit 1) 1; [reflexivity | cbn; lia].
      -- exact Anp.
      -- right. reflexivity.
      -- rewrite (df_step_long h1 b Hb0 Hov0 HnpA Apj). apply df_state_long; reflexivity.
      -- rewrite (df_step_long h1 b Hb0 Hov0 HnpA Apj). reflexivity.
      -- exact AnoW.
Qed.

(* the round's k-th byte exists while k < dnum s1: the head text holds the n bytes from the offset *)
Lemma df_ddata_nth : forall cx s1 D k p0 ly1 S1 k1 W m md e1 h1,
df_cutjh cx s1 D k p0 ly1 S1 k1 W m md e1 h1 -> Z.of_nat k < dnum s1 ->
exists b, nth_error (ddata s1) k = Some b.
Proof.
intros cx s1 D k p0 ly1 S1 k1 W m md e1 h1 HC Hk.
destruct HC as (out1 & ev1 & LB1 & spent & jb & a & v & rs & tl & r0 & rs0 &
  _ & Hpend & _ & _ & _ & HMEM & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpendm & Hoff & _).
pose proof HMEM as (_ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _).
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ahead & _).
assert (Hoff0 : 0 <= hs_off h1).
{ clear - Ahead Hpend. destruct Ahead as [(Hn & _) | (r & rs' & Hr & Ho)].
  { rewrite Hpend in Hn. discriminate. }
  lia. }
destruct (nth_error (ddata s1) k) as [b|] eqn:Hb; [exists b; reflexivity|].
exfalso. apply nth_error_None in Hb.
unfold ddata in Hb. rewrite length_firstn, length_skipn in Hb.
unfold dnum in Hb, Hk. rewrite <- Hoff in Hb, Hk. revert Hb Hk Hoff0. clear. intros. lia.
Qed.

(* ---- FEED. ----
   The loop is a do-while: s9 = dnum s1 - k is decremented at 0x83544 and tested at 0x83550, so the head
   0x8347c is re-entered only with k < dnum s1 (DRB's conjunct, W_drain_cx.v:629), and the exit to DE
   (0x835ac) is taken when k + 1 = dnum s1. *)

(* The body for a byte that the round really has.  This is the walk. *)
Lemma df_feed_step : forall cx s1 D k W1 c1,
DBASE B MT MMAX RG cx -> DRB B MT MMAX RG cx s1 D k W1 c1 ->
Z.of_nat k < dnum s1 ->
(forall W2 c2, DRB B MT MMAX RG cx s1 D (S k) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, DE B MT MMAX RG cx s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof.
intros cx s1 D k W1 c1 HB HRB Hk Hnext Hend.
destruct (df_DRB_open cx s1 D k W1 c1 HRB) as (regs1 & m1 & md1 & p0 & -> & HR & _ & HCut).
destruct HCut as (ly1 & S1 & k1 & e1 & h1 & HC).
destruct (df_ddata_nth cx s1 D k p0 ly1 S1 k1 W1 m1 md1 e1 h1 HC Hk) as (b & Hb).
exact (df_body cx s1 D k p0 ly1 S1 k1 W1 regs1 m1 md1 e1 h1 b _ HB HR Hk HC Hb Hnext Hend).
Qed.

Theorem dr_feed_p : @dr_feed_stmt fx rc SK PI B MT MMAX RG.
Proof.
unfold dr_feed_stmt. intros cx s1 D k W1 c1 HB HRB Hnext Hend.
exact (df_feed_step cx s1 D k W1 c1 HB HRB (df_DRB_bytes cx s1 D k W1 c1 HRB) Hnext Hend).
Qed.

(* ---- FEEDS: the byte loop, by induction on the bytes left. ---- *)
Theorem dr_feeds_p : @dr_feeds_stmt fx rc SK PI B MT MMAX RG.
Proof.
unfold dr_feeds_stmt. intros FEED cx s1 D k W1 c1 HB HRB HDE.
(* the loop runs at most dnum s1 - k more turns; carry that as an upper bound on the fuel *)
assert (HM : exists m : nat, (Z.to_nat (dnum s1) - k <= m)%nat)
  by (exists (Z.to_nat (dnum s1) - k)%nat; apply Nat.le_refl).
destruct HM as (m & Hm). revert k W1 c1 HRB Hm.
induction m as [|m IH]; intros k W1 c1 HRB Hm;
apply (FEED cx s1 D k W1 c1 HB HRB); try exact HDE; intros W2 c2 HRB2;
pose proof (df_DRB_bytes cx s1 D (S k) W2 c2 HRB2) as Hle;
rewrite Nat2Z.inj_succ in Hle.
- (* no byte left: a cut at S k would need S k < dnum s1 *)
  exfalso. revert Hm Hle. clear. intros Hm Hle. lia.
- apply (IH (S k) W2 c2 HRB2). revert Hm Hle. clear. intros Hm Hle. lia.
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice A, 2026-10-30): dr_feed_p_x proves W_drain_cx_x.v's dr_feed_stmt_x
   and dr_feeds_p_x its dr_feeds_stmt_x, over W_drain_cx_x.v's Section variables (the allocator rules in their
   caller-context forms, plus HP0 / BLKN / PSTR / PSTG / PSTO); the cut predicates are W_drain_cx_x.v's DRB_x (the
   loop head, after k of the n bytes) and DE_x (the loop left).  The walk is the AR walk's, with three additions:
   the source byte's block shadow is read under HP0 (W_journal_x.v range_addressable_of_block_hp0_x); list_push's
   journal keeps an image byte only off the program statics PST, so g_s (PSTG), aout_at's cells (PSTO) and the ROM
   view (PSTR) survive the call; and the room part of dbud_x: the call runs at the budget df_kr2 (the room the cut
   owes for the requests after list_push's own, df_pu_room_pre), its count premise lp_peak comes from the cut's
   counts (peak + 2 >= 2), and the cut after the push re-establishes dbud_x's room from lp_post_x and its counts
   from the block relation the post gives (df_pu_cnt: list_push changes the live counts by its requests' net count,
   W_tr_cnt.v tr_peakP_app).
   Everything above is unchanged.  The AR-free names of Section c above are CITED with the Section variables they
   abstracted; the lemmas whose statements or proofs name AR, the journal, DMEM, the cuts or the run chain have
   their _x twin here (same name with _x when the AR name exists). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt ReplyTrPeakW W_tr_cnt W_laws_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_send_line_xR.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again; and the scopes
   this file opens, again on top of the ones the imports above open *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
(* the instance's laws *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* no hidden head in any ARx state (the source byte's block shadow, W_journal_x.v Section hp0) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* a live block's size is non-negative (W_kit_x.v Section g's form; AR's al_blocks has it, the ARx blocks law not) *)
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the generic journal (YCbqG.ajournal_x) keeps an image byte only off the program statics PST: the ROM view, g_s
   and aout_at's cells off g_s survive list_push's journal.  All hold at PST = [] *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ Exists (in_zr a) PST.
Hypothesis PSTO : forall a, inG (G_SL B RG) a \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a -> ~ Exists (in_zr a) PST.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
(* the walk's globals, the allocator's statics, errno and the sink's overflow head are never read-only image
   bytes: what a callee's journal may change is disjoint from ROM, so rom_view survives it (W_journal.v
   rom_out / ajournal_gx_rom_view).  The pinned placement decides it by vm_compute. *)
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs (W_sites_x.v / W_drain_cx_x.v Section r) *)
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
(* The allocator's site rules in their caller-context forms over the generic journal (W_journal_x.v Section hc), at
   RP, one context table per allocator entry.  These two segments call no allocator entry (list_push's own calls are
   inside LPSPEC), so no site's closed trace fact is needed. *)
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
(* the allocator instance's granule-tail fact is no hypothesis: W_drain_cx_x.v alloc_tail_x, a theorem of LAWS *)
(* the callees drain calls as a program (W_contract_x.v), at RP *)
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
(* the room round's budget law (W_drain_cx_x.v RMM) *)
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
(* instance facts *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
(* placement of the three output cells aout_at reads that are not in G_DR's g_s range (W_drain_cx.v HV9 / HV12 / HSM) *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Local Notation AJGX := (ajournal_gx_x SEGS B PST ARx).

(* ---- helpers shared by the two segments (prefix df_) ---- *)

(* The byte count DRB_x carries: a cut at k has k of the n bytes behind it and at least one still to feed.
   DRB_x (W_drain_cx_x.v) has 21 existentials, then this is its 30th conjunct.  The projection is
   positional on purpose: a blanket `repeat destruct` unfolds DMEM_x / ajournal_gx_x up to conversion and does
   not finish. *)

(* The shadow entries of df_SH.  `mkSHE 23 0 96` makes every g_s field load statically covered, so the
   engine decides the `bne shadow, zero` tests at 0x83494 / 0x834a8 / 0x834d8 without leaving an
   obligation; `mkSHE 24 0 1` does the same for the source byte's check at 0x83488 and `mkSHE 26 0 1`
   for the load at 0x83490. *)
Lemma df_feed_shok_x : forall ly S Hp (W : world SEGS) mem md E HAv pk q n,
ARx ly S Hp W mem md ->
U E df_Bx = SHADOW_OFF -> U E (SOff 23 0) = HAv ->
U E (SOff 24 0) = pk -> U E (SOff 26 0) = pk ->
rg_s RG <= HAv -> HAv + 96 <= rg_s RG + 4 * ASRC ->
In (q, n) (ablocks B ly S) -> q <= pk -> pk + 1 <= q + req_size n ->
(forall x, pk <= x < pk + 1 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
sh_ok SEGS df_Bx df_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W mem md E HAv pk q n HAR HBx H23 H24 H26 HAlo HAhi Hin Hq1 Hq2 Hap.
pose proof HGSB as (HGlo & HGhi & _).
assert (HSRC : forall m, U E (SOff m 0) = pk ->
  shent_ok SEGS df_Bx E (mrestrict (w_H W) mem) (mkSHE m 0 1)).
{ intros m Hm. eapply shent_ok_of_range.
  - exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W mem md q n pk 1 HAR Hin Hq1 Hq2).
  - exact HBx.
  - exact Hm.
  - lia.
  - lia.
  - intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
    rewrite Z.add_0_r in Hx. exact (Hap x Hx). }
unfold df_SH. constructor; [|constructor; [|constructor; [|constructor]]].
- eapply shent_ok_of_range.
  + exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md (rg_s RG) (4 * ASRC) HAR HGSZ).
  + exact HBx.
  + exact H23.
  + lia.
  + lia.
  + intros x Hx. change (Z.min 0 96) with 0 in Hx. change (Z.max 0 96) with 96 in Hx.
    unfold SHADOW_OFF. unfold ASRC in *. lia.
- exact (HSRC 24%nat H24).
- exact (HSRC 26%nat H26).
Qed.

(* the allocator state (ly1, S1), its ghost list Hp1, the journal's step count k1, the relay entry e1 and the
   harness source h1 are parameters, so that a step states the rest at the witnesses it keeps and the source it
   leaves.  df_cutjt_x also names the requests still owed tl, which the list_push call splits (its room budget is
   the room of the requests after it, the cut's tl less list_push's own). *)













(* "the run left the walk's view of memory as it was": a run over a state whose regions have no window *)
Ltac df_meq MEQ :=
lazymatch goal with H : frame_of _ _ (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- _ =>
  assert (MEQ : forall x, mrestrict Hh m1 x = mrestrict Hh m0 x)
    by (intros x; apply H; intros (r & Hin & _); cbn in Hin; destruct Hin)
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Lemma df_pw_blocks_x : forall ly S Hp (W : world SEGS) m md, ARx ly S Hp W m md ->
pairwise (fun x y => zdisjoint (block_rng x) (block_rng y)) (ablocks B ly S).
Proof.
intros ly S Hp W m md HAR.
destruct (alx_sep _ _ _ LAWS ly S Hp W m md HAR) as [Hsep _].
destruct (pairwise_app_l _ _ _ Hsep) as [Hb _].
exact (df_pw_map zdisjoint block_rng (ablocks B ly S) Hb).
Qed.

(* a heap block holds no byte of g_s (blocks are not in the image, g_s is: HG) *)
Lemma df_blk_gs_x : forall ly S Hp (W : world SEGS) m md p n x,
ARx ly S Hp W m md -> In (p, n) (ablocks B ly S) -> p <= x < p + n ->
~ (rg_s RG <= x < rg_s RG + 4 * ASRC).
Proof.
intros ly S Hp W m md p n x HAR Hin Hx Hg.
pose proof (BLKN ly S Hp W m md p n HAR Hin) as Hn.
pose proof (req_size_pos n Hn) as (_ & Hrq).
apply (blk_img_x SEGS B ARx LAWS ly S Hp W m md p n x HAR Hin ltac:(lia)).
apply (proj1 (HG x ltac:(unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia))).
Qed.

(* two live blocks at different addresses share no byte *)
Lemma df_blk_out_x : forall ly S Hp (W : world SEGS) m md p n q k x,
ARx ly S Hp W m md -> In (p, n) (ablocks B ly S) -> In (q, k) (ablocks B ly S) -> p <> q ->
p <= x < p + n -> ~ (q <= x < q + k).
Proof.
intros ly S Hp W m md p n q k x HAR Hpn Hqk Hne Hx Hy.
pose proof (BLKN ly S Hp W m md p n HAR Hpn) as Hn. pose proof (BLKN ly S Hp W m md q k HAR Hqk) as Hk.
pose proof (req_size_pos n Hn) as (_ & Rn). pose proof (req_size_pos k Hk) as (_ & Rk).
pose proof (df_pw_blocks_x ly S Hp W m md HAR) as Hpw.
assert (Hne2 : (p, n) <> (q, k)) by (intros E; injection E as E1 _; exact (Hne E1)).
destruct (in_split_2 (p, n) (q, k) _ Hpn Hqk Hne2) as (l1 & l2 & l3 & [E|E]);
  pose proof (pairwise_In2 _ _ _ _ l1 l2 l3 Hpw E) as D; unfold zdisjoint, block_rng in D; cbn [fst snd] in D;
  revert Hx Hy Rn Rk D; clear; intros; lia.
Qed.

(* a byte of a live block is an address: the block lies in [4096, alloc_ceiling) *)
Lemma df_blk_rng_x : forall ly S Hp (W : world SEGS) m md p n x,
ARx ly S Hp W m md -> In (p, n) (ablocks B ly S) -> p <= x < p + n -> 0 <= x < 2 ^ 64.
Proof.
intros ly S Hp W m md p n x HAR Hin Hx.
destruct (alx_blocks _ _ _ LAWS ly S Hp W m md p n HAR Hin) as (_ & H4 & Hc & _).
pose proof (req_size_pos n (BLKN ly S Hp W m md p n HAR Hin)) as (_ & Rn).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
revert Hx H4 Hc Rn ACL. clear. intros. lia.
Qed.

Lemma df_sep_perm_x : forall ly S Hp (W : world SEGS) m md (L : list (Z * Z)),
ARx ly S Hp W m md -> Permutation (ablocks B ly S) L ->
pairwise (fun x y => zdisjoint (block_rng x) (block_rng y)) L.
Proof.
intros ly S Hp W m md L HAR HP.
exact (df_pw_perm _ df_zdisj_sym _ _ HP (df_pw_blocks_x ly S Hp W m md HAR)).
Qed.

(* the harness source after a byte that pushes nothing: only h->npartial, h->overlong and the partial buffer
   changed *)
Lemma df_asrc_upd_x : forall ly S hp (W : world SEGS) m md m' HA h1 h2,
ARx ly S hp W m md -> asrc_at B ly S W m HA h1 ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (HA + 48 <= a < HA + 60) -> ~ (hs_partial h1 <= a < hs_partial h1 + APARTIAL) ->
   abyte_kept W m W m' a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
val_mem SEGS (arm W m') (HA + 48) 8 (hs_npartial h2) -> val_mem SEGS (arm W m') (HA + 56) 4 (hs_overlong h2) ->
0 <= hs_npartial h2 <= APARTIAL -> (hs_overlong h2 = 0 \/ hs_overlong h2 = 1) ->
Z.of_nat (length (hs_pjunk h2)) = APARTIAL -> garr8 SEGS (arm W m') (hs_partial h1) (bzs (hs_pjunk h2)) ->
~ In (Z_to_bv 8 0) (hs_W h2) ->
hs_fd h2 = hs_fd h1 -> hs_open h2 = hs_open h1 -> hs_closed h2 = hs_closed h1 -> hs_eintr h2 = hs_eintr h1 ->
hs_pending h2 = hs_pending h1 -> hs_off h2 = hs_off h1 -> hs_partial h2 = hs_partial h1 ->
hs_expected h2 = hs_expected h1 -> hs_held h2 = hs_held h1 ->
asrc_at B ly S W m' HA h2.
Proof.
intros ly S hp W m md m' HA h1 h2 HAR HS HAlo HAhi KP Hpres V48 V56 Hnp2 Hov2 Hlen2 Hg2 HW2
  Efd Eop Ecl Eei Epe Eoff Epa Eex Ehe.
pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & H24).
(* slot j outside [HA + 48, HA + 60) is kept: it is image, the partial buffer is a heap block *)
assert (KH : forall x, HA <= x < HA + ASRC -> ~ (HA + 48 <= x < HA + 60) -> abyte_kept W m W m' x).
{ intros x Hx Hn. apply KP; [|exact Hn|].
  - pose proof HGSB as (G1 & G2 & _). revert Hx HAlo HAhi G1 G2. clear. unfold ASRC. intros. lia.
  - intros Hp. exact (df_blk_gs_x ly S hp W m md (hs_partial h1) APARTIAL x HAR H18 Hp ltac:(lia)). }
assert (VH : forall a n v, HA <= a -> a + Z.of_nat n <= HA + 48 ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v).
{ intros a n v Ha Hn Hv. apply (akept_vm W m); [|exact Hv]. intros x Hx. apply KH; unfold ASRC; lia. }
(* the three lists' blocks are not the partial buffer (NoDup (hs_blocks h1)) *)
assert (NP : forall p, In p (list_blocks (hs_pending h1)) \/ In p (list_blocks (hs_expected h1)) \/
  In p (list_blocks (hs_held h1)) -> p <> hs_partial h1).
{ intros p Hp Ep. subst p.
  assert (HN : NoDup (list_blocks (hs_pending h1) ++ hs_partial h1 ::
    (list_blocks (hs_expected h1) ++ list_blocks (hs_held h1)))) by exact H24.
  apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HN. apply List.NoDup_remove_2 in HN. apply HN.
  destruct Hp as [Hp | [Hp | Hp]]; apply in_or_app;
    [left; exact Hp | right; apply in_or_app; left; exact Hp | right; apply in_or_app; right; exact Hp]. }
assert (LK : forall LA l lines, HA + 16 <= LA -> LA + 16 <= HA + ASRC -> (LA + 16 <= HA + 48 \/ HA + 60 <= LA) ->
  (forall p, In p (list_blocks l) -> p <> hs_partial h1) ->
  alist_at B ly S W m LA l lines -> alist_at B ly S W m' LA l lines).
{ intros LA l lines HL1 HL2 HL3 Hnp HL. apply ((df_alist_upd B RG HGSB) ly S W m m' LA l lines HL).
  - intros x Hx. apply KH; lia.
  - intros p n x Hpn Hx.
    pose proof ((df_alist_blks_in B) ly S W m LA l lines HL (p, n) Hpn) as Hin.
    apply KP; [exact (df_blk_rng_x ly S hp W m md p n x HAR Hin Hx) | |].
    + intros Hc. exact (df_blk_gs_x ly S hp W m md p n x HAR Hin Hx ltac:(unfold ASRC in *; lia)).
    + apply (df_blk_out_x ly S hp W m md p n (hs_partial h1) APARTIAL x HAR Hin H18); [|exact Hx].
      apply Hnp. rewrite <- df_alist_blks_fst. exact (in_map fst (alist_blks l) (p, n) Hpn). }
assert (AW : awr W m' HA ASRC).
{ intros i Hi. apply (df_wr_pres W m m' (HA + i) Hpres). exact (H5 i Hi). }
unfold asrc_at, hs_blocks. rewrite Efd, Eop, Ecl, Eei, Epe, Eoff, Epa, Eex, Ehe.
split; [apply VH; [lia | cbn; lia | exact H1]|].
split; [apply VH; [lia | cbn; lia | exact H2]|].
split; [apply VH; [lia | cbn; lia | exact H3]|].
split; [apply VH; [lia | cbn; lia | exact H4]|].
split; [exact AW|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
split; [apply (LK (HA + 16) _ false); [lia | unfold ASRC; lia | lia
  | intros p Hp; apply NP; left; exact Hp | exact H10]|].
split; [apply VH; [lia | cbn; lia | exact H11]|].
split; [apply VH; [lia | cbn; lia | exact H12]|].
split; [exact V48|]. split; [exact V56|].
split; [exact H15|]. split; [exact Hnp2|]. split; [exact Hov2|]. split; [exact H18|].
split; [exact Hlen2|]. split; [exact Hg2|]. split; [exact HW2|].
split; [apply (LK (HA + 64) _ true); [lia | unfold ASRC; lia | lia
  | intros p Hp; apply NP; right; left; exact Hp | exact H22]|].
split; [apply (LK (HA + 80) _ true); [lia | unfold ASRC; lia | lia
  | intros p Hp; apply NP; right; right; exact Hp | exact H23]|].
exact H24.
Qed.


Ltac df_pu_zd i j H :=
  pose proof ((df_pu_zpw RG) _ i j (0, 0) HRGD ltac:(lia) ltac:(cbn [length]; lia)) as H;
  cbn [nth] in H; unfold zdisj in H; cbn [fst snd] in H.

(* two blocks at different positions of a permutation of the live blocks start at different addresses *)
Lemma df_pu_ne_x : forall ly S Hp (W : world SEGS) m md (x y : Z * Z) l,
ARx ly S Hp W m md -> Permutation (ablocks B ly S) (x :: y :: l) -> fst x <> fst y.
Proof.
intros ly S Hp W m md x y l HAR HP Heq.
pose proof (df_sep_perm_x ly S Hp W m md _ HAR HP) as Hpw. cbn [pairwise] in Hpw.
destruct Hpw as [Hf _]. pose proof (Forall_inv Hf) as Hd.
assert (Hx : In x (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (Hy : In y (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; left; reflexivity).
destruct x as [px nx], y as [py ny].
pose proof (req_size_pos nx (BLKN ly S Hp W m md px nx HAR Hx)) as (Rx & _).
pose proof (req_size_pos ny (BLKN ly S Hp W m md py ny HAR Hy)) as (Ry & _).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd, Heq. clear - Hd Heq Rx Ry. lia.
Qed.

Lemma df_pu_ne_in_x : forall ly S Hp (W : world SEGS) m md (x y : Z * Z) L,
ARx ly S Hp W m md -> Permutation (ablocks B ly S) (x :: L) -> In y L -> fst x <> fst y.
Proof.
intros ly S Hp W m md x y L HAR HP Hy.
destruct (in_split _ _ Hy) as (l1 & l2 & ->).
apply (df_pu_ne_x ly S Hp W m md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

(* the addresses of a stretch of a permutation of the live blocks are distinct *)
Lemma df_pu_nd_x : forall ly S Hp (W : world SEGS) m md L2 L1 L3,
ARx ly S Hp W m md -> Permutation (ablocks B ly S) (L1 ++ L2 ++ L3) -> List.NoDup (map fst L2).
Proof.
intros ly S Hp W m md L2. induction L2 as [|x L2 IH]; intros L1 L3 HAR HP; [apply List.NoDup_nil|].
cbn [map]. apply List.NoDup_cons.
- intros Hin. apply in_map_iff in Hin as (y & Hy & Hin).
  assert (HP2 : Permutation (ablocks B ly S) (x :: L1 ++ L2 ++ L3)).
  { eapply Permutation_trans; [exact HP|]. cbn [app]. apply Permutation_sym, Permutation_middle. }
  exact (df_pu_ne_in_x ly S Hp W m md x y (L1 ++ L2 ++ L3) HAR HP2
    ltac:(apply in_or_app; right; apply in_or_app; left; exact Hin) (eq_sym Hy)).
- apply (IH (L1 ++ [x]) L3 HAR). rewrite <- app_assoc. exact HP.
Qed.

(* ---- THE ROOM AND THE COUNTS across the push (W_drain_cx_x.v dbud_x's two conjuncts): MT_rk's charge of a trace and
   of list_push, and the live counts the push leaves against the counts and peak the cut owed. ---- *)
Lemma df_rk_cost_app : forall (t1 t2 : dtrace), tr_cost MT_rk (t1 ++ t2) = tr_cost MT_rk t1 + tr_cost MT_rk t2.
Proof.
intros t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

Lemma df_rk_cost_nn : forall (t : dtrace), 0 <= tr_cost MT_rk t.
Proof.
induction t as [|ev t IH]; [unfold tr_cost; cbn; lia|].
change (ev :: t) with ([ev] ++ t). rewrite df_rk_cost_app.
assert (0 <= tr_cost MT_rk [ev]) by (destruct ev; unfold tr_cost, MT_rk; cbn; lia).
lia.
Qed.

(* df_pu_lp_cost at any meter *)
Lemma df_lp_cost_g : forall MT0 (l : hlist) (v : dadrF) n,
lp_cost MT0 l n + mo_free MT0 = tr_cost MT0 (ListTr.list_push_tra v (hl_n l) (hl_cap l) n).
Proof.
intros MT0 l v n. unfold lp_cost, lp_grow, lp_vbytes, ListTr.list_push_tra, tr_cost, ListRep.grow_cap.
destruct (hl_n l =? hl_cap l); [destruct (hl_cap l =? 0)|]; cbn [app fold_right].
- replace (AREC * 8) with 128 by (unfold AREC; lia). lia.
- replace (AREC * (2 * hl_cap l)) with (32 * hl_cap l) by (unfold AREC; lia). lia.
- lia.
Qed.

Lemma df_rk_lp_nn : forall (l : hlist) n, 0 <= lp_cost MT_rk l n.
Proof.
intros l n. unfold lp_cost. assert (M : forall x, mo_malloc MT_rk x = 1) by (intros; reflexivity).
assert (F : mo_free MT_rk = 1) by reflexivity. rewrite !M, F. destruct (lp_grow l); lia.
Qed.

(* the budget list_push is given: the room of the requests the cut owes after list_push's own, MT_rk's charge of tl
   less list_push's charge and its one free *)
Definition df_kr2 (l : hlist) (n : Z) (tl : dtrace) (kr : nat) : nat :=
(Z.to_nat (tr_cost MT_rk tl - lp_cost MT_rk l n - 1) + kr)%nat.

Lemma df_kr2_eq : forall (l : hlist) (v : dadrF) N C n n' tl' kr, hl_n l = N -> hl_cap l = C -> n = n' ->
df_kr2 l n' (ListTr.list_push_tra v N C n ++ tl') kr = (Z.to_nat (tr_cost MT_rk tl') + kr)%nat.
Proof.
intros l v N C n n' tl' kr EN EC En. subst N C n. unfold df_kr2.
rewrite df_rk_cost_app, <- (df_lp_cost_g MT_rk l v n').
assert (F : mo_free MT_rk = 1) by reflexivity. rewrite F. lia.
Qed.

(* the call's room premise, from the cut's room (W_drain_cx_x.v RMM drops list_push's free) *)
Lemma df_pu_room_pre : forall S1 (l : hlist) (v : dadrF) N C n n' tl' kr, hl_n l = N -> hl_cap l = C -> n = n' ->
rp_RM RP S1 (Z.to_nat (tr_cost MT_rk (ListTr.list_push_tra v N C n ++ tl')) + kr) ->
rp_RM RP S1 (Z.to_nat (lp_cost MT_rk l n') + df_kr2 l n' (ListTr.list_push_tra v N C n ++ tl') kr).
Proof.
intros S1 l v N C n n' tl' kr EN EC En H. rewrite (df_kr2_eq l v N C n n' tl' kr EN EC En). subst N C n.
eapply RMM; [|exact H].
rewrite df_rk_cost_app, <- (df_lp_cost_g MT_rk l v n').
pose proof (df_rk_cost_nn tl'). pose proof (df_rk_lp_nn l n').
assert (F : mo_free MT_rk = 1) by reflexivity. rewrite F. lia.
Qed.

(* the counts after the push: list_push's requests change the live counts by their net count, so the counts of the
   requests still owed plus their peak stay within what the cut owed (W_tr_cnt.v tr_peakP_app: the peak of a ++ b is at
   least the net count of a plus the peak of b) *)
Lemma df_pu_cnt : forall (l : hlist) (v : dadrF) N C n n' tl' (L1 L2 OV OV2 R0 : list (Z * Z)) d v2,
hl_n l = N -> hl_cap l = C -> n = n' ->
Permutation L1 (OV ++ R0) -> Permutation L2 ((d, n' + 1) :: OV2 ++ R0) ->
OV = (if C =? 0 then [] else [(hl_v l, AREC * C)]) ->
OV2 = (if N =? C then [(v2, AREC * ListRep.grow_cap N C)] else OV) ->
cnt_ok_pk RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P (ListTr.list_push_tra v N C n ++ tl')) + 2)%nat) L1 ->
cnt_ok_pk RP (fun P => (Z.to_nat (ReplyCnt.tr_peakP P tl') + 2)%nat) L2.
Proof.
intros l v N C n n' tl' L1 L2 OV OV2 R0 d v2 EN EC En P1 P2 EOV EOV2 HC. subst n'.
eapply (cnt_ok_pk_mono RP _ _ L1 L2); [|exact HC].
intros P. cbv beta.
rewrite (ReplyCnt.acnt_perm P _ _ P1), (ReplyCnt.acnt_perm P _ _ P2), acnt_cons, !ReplyCnt.acnt_app. cbn [snd].
rewrite W_tr_cnt.tr_peakP_app.
pose proof (ReplyCnt.tr_peakP_nonneg _ P tl') as N0.
assert (KEY : Z.of_nat (ReplyCnt.acnt P OV2) + ReplyCnt.zb (P (n + 1)) =
  Z.of_nat (ReplyCnt.acnt P OV) + W_tr_cnt.tr_netP P (ListTr.list_push_tra v N C n)).
{ subst OV OV2. unfold ListTr.list_push_tra, ListRep.grow_cap, AREC.
  rewrite W_tr_cnt.tr_netP_app.
  destruct (Z.eqb_spec N C) as [E1|E1]; [destruct (Z.eqb_spec C 0) as [E2|E2]|]; cbv iota;
  unfold W_tr_cnt.tr_netP, ReplyTrPeakW.tr_net_w, ReplyCnt.acnt; cbn [fold_right map List.filter snd length app].
  - replace (16 * 8) with 128 by reflexivity. unfold ReplyCnt.zb.
    destruct (P 128), (P (n + 1)); cbn [length]; lia.
  - replace (16 * (2 * C)) with (32 * C) by lia. unfold ReplyCnt.zb.
    destruct (P (32 * C)), (P (16 * C)), (P (n + 1)); cbn [length]; lia.
  - unfold ReplyCnt.zb. destruct (Z.eqb_spec C 0); cbv iota; cbn [map List.filter snd length];
    [destruct (P (n + 1)); cbn [length]; lia | destruct (P (16 * C)), (P (n + 1)); cbn [length]; lia]. }
unfold ReplyCnt.zb in KEY. destruct (P (n + 1)); cbv iota in KEY |- *; lia.
Qed.

Ltac df_pu_in := first [ assumption | solve [left; reflexivity] | solve [apply in_or_app; left; df_pu_in]
  | solve [apply in_or_app; right; df_pu_in] | solve [right; df_pu_in] ].

(* the NUL byte with h->overlong = 0: list_push (h->expected, h->partial, h->npartial) at 0x834f0, then
   h->npartial = 0 and h->overlong = 0.  l2 is the list list_push leaves (lp_post_x), d its new text's block;
   the state is the one the two stores leave at 0x83544.  The cut is taken at its requests tl (df_cutjt_x): the room
   list_push leaves is the budget df_kr2 the call was given, the room of the requests after list_push's. *)


(* The end of an arm that wrote only h->npartial and h->overlong (skip, long, reset): the cut after the byte,
   then the tail. *)


(* a run's write permission when the regions write only slot j's fields *)
Ltac df_awr U23 HAe :=
apply (df_awr_gs B RG HGSB); [vm_compute; reflexivity
  | cbn [ew ewset Nat.eqb]; rewrite U23, HAe; unfold ASRC in *; lia
  | cbn [ew ewset Nat.eqb]; rewrite U23, HAe; unfold ASRC in *; lia].

(* carry "the walk's view outside df_Pg is m's" and "m's present bytes are present" across the last run *)
Ltac df_track m MEQ PR U23 :=
lazymatch goal with
| HF : frame_of ?Ex ?rs (mrestrict ?Hh ?mc) (mrestrict ?Hh ?mn),
  HGr : mem_grows (mrestrict ?Hh ?mc) (mrestrict ?Hh ?mn) |- _ =>
  let MEQ' := fresh "MEQ" in let PR' := fresh "PR" in
  pose proof (df_meq_step Ex rs Hh m mc mn _ MEQ HF
    ltac:(intros a Ha; pose proof ((df_wrange_gs RG HGSB) Ex rs a ltac:(vm_compute; reflexivity) Ha) as Hw;
          cbn [ew ewset Nat.eqb] in Hw; rewrite U23 in Hw; exact Hw)) as MEQ';
  assert (PR' : forall a, apresent Hh m a -> apresent Hh mn a)
    by (intros a Ha; exact (apresent_grows Hh mc mn a HGr (PR a Ha)));
  clear MEQ PR; rename MEQ' into MEQ; rename PR' into PR;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
end.

(* rewrite the denotation of an extra atom inside a branch condition, whatever the run's environment *)
Ltac df_Uat Hc n v Ev Rv :=
lazymatch type of Hc with context [U ?Ex (SOff n 0)] =>
  rewrite (U_atom Ex n v ltac:(cbn [ew ewset Nat.eqb]; exact Ev) Rv) in Hc
end.
Ltac df_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
end.

Ltac df_ra HS EE n r :=
let Q := fresh "Q" in df_reg HS r Q;
apply (df_reg_atom _ _ _ _ _ n Q); cbn [ew ewset Nat.eqb]; exact (EE n r eq_refl).

Ltac df_rs HS E23 E21 HAr r c Rr :=
let Q := fresh "Q" in df_reg HS r Q; rewrite Rr;
apply ((df_reg_shv RG) _ _ r 23%nat c _ Q);
[ cbn [ew ewset Nat.eqb]; exact E23 | cbn [ew ewset Nat.eqb]; exact E21
| clear - HAr; lia | clear - HAr; lia ].

(* the loop's registers are the body's callee-kept ones: the body writes only a0..a3 *)
Ltac df_regs_tac HS HR EE E23 E21 HAr R20 R27 R22 :=
apply ((df_regs_keep RG) _ _ _ _ _ _ HR);
[ df_ra HS EE 2%nat (2%bv : bv 5) | df_ra HS EE 3%nat (3%bv : bv 5) | df_ra HS EE 4%nat (4%bv : bv 5)
| df_ra HS EE 18%nat (18%bv : bv 5) | df_ra HS EE 9%nat (9%bv : bv 5) | df_ra HS EE 8%nat (8%bv : bv 5)
| df_ra HS EE 21%nat (21%bv : bv 5) | df_ra HS EE 23%nat (23%bv : bv 5) | df_ra HS EE 19%nat (19%bv : bv 5)
| df_ra HS EE 25%nat (25%bv : bv 5) | df_ra HS EE 26%nat (26%bv : bv 5) | df_ra HS EE 24%nat (24%bv : bv 5)
| df_rs HS E23 E21 HAr (20%bv : bv 5) 40 R20 | df_rs HS E23 E21 HAr (27%bv : bv 5) 48 R27
| df_rs HS E23 E21 HAr (22%bv : bv 5) 56 R22 ].

(* an arm's end: run to the tail 0x83544, carry the memory facts, name slot j's region (index i of the final
   state's regions) RG1, and put the goal in mkst form *)
Ltac df_leaf_run HS HJ SHOK U23 HAe m MEQ PR i :=
paj_run_to_tok_x RUNTO HS HJ SHOK DFspan A_df_tail; [df_awr U23 HAe|];
df_track m MEQ PR U23;
let RG1 := fresh "RG1" in
pose proof (st_ok_pi_region_nth _ _ _ i _ HS eq_refl) as RG1; cbn [ms_mem restrict] in RG1;
pmkst HS.

Ltac df_inc := repeat (first [left; reflexivity | right]).

(* a field of slot j in the final state; left: its denotation and its range *)
Ltac df_v HA U23 od w e v :=
lazymatch goal with RG1 : region_ok _ _ _ (YP09.mkRegion (Some 23%nat) _ _ _ _ _) |- _ =>
unfold arm; eapply (field_of_region _ _ 23%nat HA _ _ _ _ _ od w e v RG1);
[ cbn [ew ewset Nat.eqb]; exact U23 | cbn [In]; df_inc | | | cbn; lia ]
end.

(* a live block's byte is kept by a run that writes only slot j's fields 48..60 *)
Lemma df_heap_keep_x : forall ly S Hp (W : world SEGS) m md m' HA p n a,
ARx ly S Hp W m md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
(forall x : word, ~ df_Pg HA (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
(forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
abyte_kept W m W m' a.
Proof.
intros ly S Hp W m md m' HA p n a HAR Hin Ha HAlo HAhi HM HP.
destruct (alx_blocks _ _ _ LAWS ly S Hp W m md p n HAR Hin) as (_ & H4 & Hc & _).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
apply ((df_keep_of_meq RG) W m m' (df_Pg HA) HM HP a); [clear - Ha H4 Hc ACL; lia|].
intros Hg. apply (blk_img_x SEGS B ARx LAWS ly S Hp W m md p n a HAR Hin Ha).
unfold df_Pg in Hg.
apply (proj1 (HG a ltac:(unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
  unfold ASRC in HAlo, HAhi |- *; clear - Hg HAlo HAhi; lia))).
Qed.

Lemma df_heap_np_x : forall ly S Hp (W : world SEGS) m md HA p n a,
ARx ly S Hp W m md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
(0 <= a < 2 ^ 64) /\ ~ df_Pg HA a.
Proof.
intros ly S Hp W m md HA p n a HAR Hin Ha HAlo HAhi.
destruct (alx_blocks _ _ _ LAWS ly S Hp W m md p n HAR Hin) as (_ & H4 & Hc & _).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
split; [clear - Ha H4 Hc ACL; lia|].
intros Hg. apply (blk_img_x SEGS B ARx LAWS ly S Hp W m md p n a HAR Hin Ha).
unfold df_Pg in Hg.
apply (proj1 (HG a ltac:(unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
  unfold ASRC in HAlo, HAhi |- *; clear - Hg HAlo HAhi; lia))).
Qed.

(* aout_at's three cells off g_s and errno are off the program statics PST (PSTO) *)
Lemma df_cell_pst : forall a,
(rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_client RG <= a < rg_client RG + 4) \/
(rg_send_dead RG <= a < rg_send_dead RG + 1) \/ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST.
Proof.
intros a Ha. apply PSTO. unfold inG.
destruct Ha as [H|[H|[H|H]]]; [right | right | right | left; unfold G_SL].
- do 2 apply Exists_cons_tl. apply Exists_cons_hd. exact H.
- apply Exists_cons_hd. exact H.
- apply Exists_cons_tl. apply Exists_cons_hd. exact H.
- do 5 apply Exists_cons_tl. apply Exists_cons_hd. exact H.
Qed.

(* ---- df_push_pre_x's helpers.  The requests still to come ask for no negative size (SlotP4Res3Aux.v drain_inv's
   invariant over the model: the three capacities stay >= 0), so their cost and their bytes are >= 0. ---- *)

(* ---- The NUL byte with h->overlong = 0: the call list_push (&h->expected, h->partial, h->npartial). ----
   df_push_pre_x: what lp_spec_x asks of the call, read off the cut at its requests tl (the source, the budget, the
   footprint; the room for list_push and the requests after it, df_kr2; the counts within list_push's peak). *)
Lemma df_lp_rq_out_x : forall ly S Hp (W : world SEGS) m md p n q k x,
ARx ly S Hp W m md -> In (p, n) (ablocks B ly S) -> In (q, k) (ablocks B ly S) -> p <> q ->
p <= x < p + req_size n -> ~ (q <= x < q + req_size k).
Proof.
intros ly S Hp W m md p n q k x HAR Hpn Hqk Hne Hx Hy.
pose proof (df_pw_blocks_x ly S Hp W m md HAR) as Hpw.
assert (Hne2 : (p, n) <> (q, k)) by (intros E; injection E as E1 _; exact (Hne E1)).
destruct (in_split_2 (p, n) (q, k) _ Hpn Hqk Hne2) as (l1 & l2 & l3 & [E|E]);
  pose proof (pairwise_In2 _ _ _ _ l1 l2 l3 Hpw E) as D; unfold zdisjoint, block_rng in D; cbn [fst snd] in D;
  revert Hx Hy D; clear; intros; lia.
Qed.

(* list_push's footprint (its vector, when it has one) is a heap block: positive, and apart from every other
   live block *)
Lemma df_lpfp_pos_x : forall ly S Hp (W : world SEGS) m md LA (l : hlist) lines,
ARx ly S Hp W m md -> alist_at B ly S W m LA l lines -> ~ YI16.sink_open_fp (lp_FP l).
Proof.
intros ly S Hp W m md LA l lines HAR HL.
pose proof HL as (_ & _ & _ & _ & _ & Hvec & _).
apply sink_closed_pos. unfold lp_FP.
destruct (Z.eqb_spec (hl_cap l) 0) as [Hc | Hc]; [constructor|].
destruct Hvec as [[Hc0 _] | (_ & Hv & _)]; [exfalso; exact (Hc Hc0)|].
destruct (alx_blocks _ _ _ LAWS ly S Hp W m md _ _ HAR Hv) as (_ & H4096 & _).
constructor; [cbn [fst]; clear - H4096; lia | constructor].
Qed.

Lemma df_lpfp_out_x : forall ly S Hp (W : world SEGS) m md LA (l : hlist) lines p n,
ARx ly S Hp W m md -> alist_at B ly S W m LA l lines -> In (p, n) (ablocks B ly S) -> p <> hl_v l ->
forall i, 0 <= i < req_size n -> ~ inFP (lp_FP l) (p + i).
Proof.
intros ly S Hp W m md LA l lines p n HAR HL Hin Hne i Hi.
pose proof HL as (_ & _ & _ & _ & _ & Hvec & _).
unfold lp_FP. destruct (Z.eqb_spec (hl_cap l) 0) as [Hc | Hc]; [intros (r & [] & _)|].
destruct Hvec as [[Hc0 _] | (_ & Hv & _)]; [exfalso; exact (Hc Hc0)|].
intros (r & [<- | []] & Hr). cbn [fst snd] in Hr.
pose proof (req_size_pos _ (BLKN ly S Hp W m md _ _ HAR Hv)) as (_ & Rn).
apply (df_lp_rq_out_x ly S Hp W m md p n (hl_v l) (AREC * hl_cap l) (p + i) HAR Hin Hv Hne ltac:(clear - Hi; lia)).
clear - Hr Rn. lia.
Qed.




(* the call, journal to journal (W_source_reset.v:442 aj_gx_call at G := G_DR; W_gesture_end.v gx_callS's _x form) *)
Lemma df_gx_call_x : forall (G1 : list (Z * Z)) (W : world SEGS) regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc
Hpc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Z -> Prop),
(forall a, inG G1 a -> inG (G_DR B RG) a) ->
AJGX (G_DR B RG) 0 [] STK sp0 FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memT) (sp0 + o) (s0Z regsT) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsT memT mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  AJGX G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsT regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2 k1)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 AJGX (G_DR B RG) 0 [] STK sp0 FP ly S Hp W0 mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 AJGX G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsT regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2 k1).
Proof.
intros G1 W regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
HGsub HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee.
  destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  eapply (afn_pre_x_at SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md [] lyc Sc Hpc W memT mdc k regsT STK1 o ch1 HJi);
    try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
split; [|split; [exact HJ1 | split; [exact HP | exact HK]]].
replace (@nil (Z * Z)) with ([] ++ @nil (Z * Z)) by reflexivity.
eapply (ajournal_gx_sub_x SEGS B PST ARx LAWS pa_segs_low);
[ exact HJ
| exact (ajournal_gx_G_mono_x SEGS B PST ARx G1 (G_DR B RG) 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2
    Hp2 W2 mem2 md2 k1 HGsub HJ1)
| clear - Hneg Hbud; lia | clear - Hneg; lia | clear - Hneg; lia | intros a (r & [] & _) | exact HG | exact HF ].
Qed.
Lemma df_gx_call_xR {R : world SEGS -> world SEGS -> Prop} (R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) :
forall (G1 : list (Z * Z)) (W : world SEGS) regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc
Hpc mdc k STK1 FP1 (o : Z) raw ch1
(K : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Z -> Prop),
(forall a, inG G1 a -> inG (G_DR B RG) a) ->
ajournal_gx_xR SEGS B PST ARx R (G_DR B RG) 0 [] STK sp0 FP ly S Hp W0 mem md [] lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memT) (sp0 + o) (s0Z regsT) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsT memT mdc ch1 ->
 SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsT regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2 k1)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R (G_DR B RG) 0 [] STK sp0 FP ly S Hp W0 mem md [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_xR SEGS B PST ARx R G1 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsT regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2 k1).
Proof.
intros G1 W regsT memT pc STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
HGsub HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRrG_mono.
{ apply Hcallee.
  destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
  rewrite !Z.add_0_r in HJi.
  eapply (afn_pre_x_atR SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md [] lyc Sc Hpc W memT mdc k regsT STK1 o ch1 HJi);
    try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
split; [|split; [exact HJ1 | split; [exact HP | exact HK]]].
replace (@nil (Z * Z)) with ([] ++ @nil (Z * Z)) by reflexivity.
eapply (ajournal_gx_sub_xR SEGS B PST ARx LAWS pa_segs_low R_trans);
[ exact HJ
| exact (ajournal_gx_G_mono_xR SEGS B PST ARx G1 (G_DR B RG) 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memT mdc [] ly2 S2
    Hp2 W2 mem2 md2 k1 HGsub HJ1)
| clear - Hneg Hbud; lia | clear - Hneg; lia | clear - Hneg; lia | intros a (r & [] & _) | exact HG | exact HF ].
Qed.


Lemma df_blk_wr_x : forall ly S Hp (W : world SEGS) mem md b n,
ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n ->
writable_at SEGS (mrestrict (w_H W) mem) (b + i).
Proof.
intros ly S Hp W mem md b n HAR Hin i Hi. apply (apresent_writable SEGS).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hin) as (_ & _ & _ & _ & Hpr & _).
exact (proj1 (Hpr (b + i) ltac:(clear - Hi; lia))).
Qed.

(* df_lp_call_x: the call itself, through LPSPEC at G = [(&h->expected, 16)], composed into drain's journal
   (W_source_reset.v aj_gx_call's shape), at the budget kr2 the caller gives (the call's room premise); the
   continuation gets the call's effect on memory as the keep facts df_close_push_x takes, and the room it leaves. *)
Lemma df_blk_out_rq_x : forall ly S Hp (W : world SEGS) m md p n q k x,
ARx ly S Hp W m md -> In (p, n) (ablocks B ly S) -> In (q, k) (ablocks B ly S) -> p <> q ->
p <= x < p + req_size n -> ~ (q <= x < q + req_size k).
Proof.
intros ly S Hp W m md p n q k x HAR Hpn Hqk Hne Hx Hy.
pose proof (df_pw_blocks_x ly S Hp W m md HAR) as Hpw.
assert (Hne2 : (p, n) <> (q, k)) by (intros E; injection E as E1 _; exact (Hne E1)).
destruct (in_split_2 (p, n) (q, k) _ Hpn Hqk Hne2) as (l1 & l2 & l3 & [E|E]);
  pose proof (pairwise_In2 _ _ _ _ l1 l2 l3 Hpw E) as D; unfold zdisjoint, block_rng in D; cbn [fst snd] in D;
  revert Hx Hy D; clear; intros; lia.
Qed.




(* ---- FEED. ----
   The loop is a do-while: s9 = dnum s1 - k is decremented at 0x83544 and tested at 0x83550, so the head
   0x8347c is re-entered only with k < dnum s1 (DRB_x's conjunct), and the exit to DE_x (0x835ac) is taken when
   k + 1 = dnum s1. *)





(* ---- route R: the R twin of each piece of Section cx whose statement names the journal, SRr, a carrier or
   a statement: the strict text with the journal and SRr at R and each carrier / statement / engine lemma at its R
   twin (W_drain_cx_x.v Section wR). The strict lemmas above are unchanged. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
Local Notation AJGXR := (ajournal_gx_xR SEGS B PST ARx R).
Hypothesis SLSPECR : sl_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPECR : lp_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_list_push).
Ltac df_leaf_runR HS HJ SHOK U23 HAe m MEQ PR i :=
paj_run_to_tok_xR RUNTOR HS HJ SHOK DFspan A_df_tail; [df_awr U23 HAe|];
df_track m MEQ PR U23;
let RG1 := fresh "RG1" in
pose proof (st_ok_pi_region_nth _ _ _ i _ HS eq_refl) as RG1; cbn [ms_mem restrict] in RG1;
pmkst HS.

Lemma df_DRB_bytes_xR : forall cx Hp kr s1 D k W1 c1,
DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D k W1 c1 -> Z.of_nat k < dnum s1.
Proof.
intros cx Hp kr s1 D k W1 c1 H.
destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
  ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
  ? & ? & ? & ? & ? & ? & ? & ? & ? & Hk & ?).
exact Hk.
Qed.

Definition df_cutjt_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (p0 : Z)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (k1 : Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model)
(e1 : rentry) (h1 : hsrc) (tl : dtrace) : Prop :=
exists out1 ev1 LB1 spent jb a v rs r0 rs0,
(df_slots RG) cx W1 m1 /\
hl_recs (hs_pending h1) = r0 :: rs0 /\ p0 = fst r0 + drain_b_c.ds_off s1 /\
0 < dnum s1 /\
bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 /\
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DSAME cx e1 h1 /\
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
hs_eintr h1 = 0 /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend s1 /\
hs_off h1 = drain_b_c.ds_off s1 /\
hs_state h1 = feed (drain_b_c.ds_ref s1) (firstn k (ddata s1)) /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1)))) /\
hl_cap (hs_expected h1) =
  pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1))) /\
DHIST cx s1 D (D ++ firstn k (ddata s1)) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
RSTART cx s1 D /\
dpfut cx s1 k jb a v rs tl /\ dbud_x B MT RP MMAX cx kr ly1 S1 spent tl.

Definition df_cutjh_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (p0 : Z)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (k1 : Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model)
(e1 : rentry) (h1 : hsrc) : Prop :=
exists tl, df_cutjt_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W1 m1 md1 e1 h1 tl.

Definition df_cutj_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (p0 : Z)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (k1 : Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model)
: Prop :=
exists e1 h1, df_cutjh_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W1 m1 md1 e1 h1.

Definition df_cut_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (p0 : Z)
(W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) : Prop :=
exists ly1 S1 Hp1 k1, df_cutj_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W1 m1 md1.

Lemma df_DRB_open_xR : forall cx Hp kr s1 D k W1 c1, DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D k W1 c1 ->
exists regs1 m1 md1 p0, c1 = cfg_at SEGS (BASE + A_dr_feed) regs1 m1 md1 /\ (df_regs RG) cx s1 p0 k regs1 /\
Z.of_nat k < dnum s1 /\ df_cut_xR cx Hp kr s1 D k p0 W1 m1 md1.
Proof.
intros cx Hp kr s1 D k W1 c1 H.
destruct H as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & v & rs & tl &
  p0 & r0 & rs0 &
  Hcfg & R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22 &
  HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192 &
  Hpend & Hp0 & Hk & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
exists regs1, m1, md1, p0.
split; [exact Hcfg|].
split; [exact (conj R2 (conj R3 (conj R4 (conj R18 (conj R9 (conj R8 (conj R21 (conj R23 (conj R19
  (conj R25 (conj R26 (conj R24 (conj R20 (conj R27 R22))))))))))))))|].
split; [exact Hk|].
exists ly1, S1, Hp1, k1, e1, h1, tl, out1, ev1, LB1, spent, jb, a, v, rs, r0, rs0.
exact (conj (conj HFR (conj M56 (conj M64 (conj M48 (conj M200 (conj M32 (conj M24 (conj M72 (conj M80 (conj
  M40 M192)))))))))) (conj Hpend (conj Hp0 (conj Hn0 (conj Hdata (conj HMEM (conj HnoNUL (conj Hused (conj
  HSAME (conj Hcap (conj Hu (conj Hskip (conj Hkeys (conj Hka (conj Heintr (conj Hpendm (conj Hoff (conj Hstate
  (conj Hen (conj Hecap (conj HHIST (conj HRS (conj HPFUT HBUD))))))))))))))))))))))).
Qed.

Lemma df_DRB_close_xR : forall cx Hp kr s1 D k p0 W1 regs1 m1 md1,
(df_regs RG) cx s1 p0 k regs1 -> Z.of_nat k < dnum s1 -> df_cut_xR cx Hp kr s1 D k p0 W1 m1 md1 ->
DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D k W1 (cfg_at SEGS (BASE + A_dr_feed) regs1 m1 md1).
Proof.
intros cx Hp kr s1 D k p0 W1 regs1 m1 md1
  (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22) Hk HC.
destruct HC as (ly1 & S1 & Hp1 & k1 & e1 & h1 & tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) &
  Hpend & Hp0 & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
exists regs1, ly1, S1, Hp1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent, jb, a, v, rs, tl, p0, r0, rs0.
exact (conj eq_refl (conj R2 (conj R3 (conj R4 (conj R18 (conj R9 (conj R8 (conj R21 (conj R23 (conj R19 (conj
  R25 (conj R26 (conj R24 (conj R20 (conj R27 (conj R22 (conj HFR (conj M56 (conj M64 (conj M48 (conj M200
  (conj M32 (conj M24 (conj M72 (conj M80 (conj M40 (conj M192 (conj Hpend (conj Hp0 (conj Hk (conj Hn0 (conj
  Hdata (conj HMEM (conj HnoNUL (conj Hused (conj HSAME (conj Hcap (conj Hu (conj Hskip (conj Hkeys (conj Hka
  (conj Heintr (conj Hpendm (conj Hoff (conj Hstate (conj Hen (conj Hecap (conj HHIST (conj HRS (conj HPFUT
  HBUD)))))))))))))))))))))))))))))))))))))))))))))))))).
Qed.

Lemma df_DE_close_xR : forall cx Hp kr s1 D kk p0 W1 regs1 m1 md1,
(df_regs RG) cx s1 p0 kk regs1 -> df_cut_xR cx Hp kr s1 D (Z.to_nat (dnum s1)) p0 W1 m1 md1 ->
DE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W1 (cfg_at SEGS (BASE + A_dr_fed) regs1 m1 md1).
Proof.
intros cx Hp kr s1 D kk p0 W1 regs1 m1 md1
  (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & _) HC.
destruct HC as (ly1 & S1 & Hp1 & k1 & e1 & h1 & tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) &
  Hpend & Hp0 & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
rewrite (df_firstn_ddata s1) in Hstate, Hen, Hecap, HHIST.
unfold dpfut in HPFUT. cbv zeta in HPFUT.
rewrite (df_firstn_ddata s1), ((df_skipn_ddata RG HGSB) s1), df_lines_nil in HPFUT.
cbn [drain_b_c.pushes_run fst snd app] in HPFUT.
destruct HPFUT as (tl2 & Hdr & Htl). subst tl.
exists regs1, ly1, S1, Hp1, m1, md1, k1, e1, h1, out1, ev1, LB1, spent.
eexists. eexists. exists tl2.
exact (conj eq_refl (conj R2 (conj R3 (conj R4 (conj R18 (conj R9 (conj R8 (conj R21 (conj R23 (conj R19 (conj
  HFR (conj M56 (conj M64 (conj M48 (conj M200 (conj M32 (conj M80 (conj M40 (conj M192 (conj Hn0 (conj Hdata
  (conj HMEM (conj HnoNUL (conj Hused (conj HSAME (conj Hcap (conj Hu (conj Hskip (conj Hkeys (conj Hka (conj
  Heintr (conj Hpendm (conj Hoff (conj Hstate (conj Hen (conj Hecap (conj HHIST (conj HRS (conj Hdr
  HBUD))))))))))))))))))))))))))))))))))))))).
Qed.

Lemma df_dmem_rebuild_xR : forall cx Hp ly S Hp1 W m md k e h s out ev sent LB ly' S' Hp' W' m' md' k' h',
DMEM_xR B PST ARx RG R cx Hp ly S Hp1 W m md k e h s out ev sent LB ->
AJGXR (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly' S' Hp' W' m' md' k' ->
rom_view SEGS W' m' ->
apres_kept B W m W' m' -> frames S' = frames S ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
(forall a, dxSA cx <= a < dxSA cx + AENT -> abyte_kept W m W' m' a) ->
akept W m W' m' (aentry_fp e) ->
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= a < dHA RG cx + ASRC) ->
   abyte_kept W m W' m' a) ->
akept W m W' m' (aout_fp B RG (drain_b_c.ds_ocap s) out) ->
asrc_at B ly' S' W' m' (dHA RG cx) h' ->
Permutation (ablocks B ly' S')
  ((dxG cx, ATABLE) :: aentry_blks e ++ asrc_blks h' ++ aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) ->
DMEM_xR B PST ARx RG R cx Hp ly' S' Hp' W' m' md' k' e h' s out ev sent LB.
Proof.
intros cx Hp ly S Hp1 W m md k e h s out ev sent LB ly' S' Hp' W' m' md' k' h' HD HJ' KR KP KF KS KA KE KG KO HS' HP'.
destruct HD as (HJ & Hrom & Hpres & Hfr & HFR & Hent & Hawr & Hokx & Hsrc & Hoth & Hgsk & Hout & Hlive & Hperm).
assert (HIN : forall b, In b (aentry_blks e) \/ In b (aout_blks (drain_b_c.ds_ocap s) out) ->
  In b (ablocks B ly' S')).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HP'|]. right.
  destruct Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb|right].
  apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (VK : forall a n v, dsp0 cx - DRAIN_FRAME <= a -> a + Z.of_nat n <= dsp0 cx ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W' m') a n v).
{ intros a n v H1 H2 Hv. apply (akept_vm W m); [intros x Hx; apply KS; lia | exact Hv]. }
pose proof Hokx as (_ & _ & P1 & P2 & _).
split; [exact HJ'|].
split; [exact KR|].
split; [intros a H1 H2 H3 H4; exact (KP a H1 H2 H3 (Hpres a H1 H2 H3 H4))|].
split; [rewrite KF; exact Hfr|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FS).
  unfold DRAIN_FRAME in VK |- *.
  repeat split; try (apply VK; [simpl Z.of_nat; lia | simpl Z.of_nat; lia | assumption]).
  unfold dr_saved. intros i Hi. apply VK; [lia | simpl Z.of_nat; lia | exact (FS i Hi)]. }
split.
{ apply (akept_garr8 W m); [|exact Hent].
  intros x Hx. rewrite (df_entry_len e P1 P2) in Hx. apply KA. unfold AENT. simpl Z.of_nat in Hx. lia. }
split; [apply (akept_awr W m); [intros x Hx; apply KA; exact Hx | exact Hawr]|].
split; [exact ((df_aentry_okx_kept B RG) ly S W m ly' S' W' m' e Hokx KE (fun b Hb => HIN b (or_introl Hb)))|].
split; [exact HS'|].
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Vo). exists f, o.
  assert (KI : forall x, rg_s RG + ASRC * Z.of_nat i <= x < rg_s RG + ASRC * Z.of_nat i + 8 ->
    abyte_kept W m W' m' x).
  { intros x Hx. apply KG; unfold dHA, ASRC in *; [lia|]. intros Hc. apply Hij. lia. }
  split; [|split; [|exact Vo]]; (apply (akept_vm W m); [intros x Hx; apply KI; simpl Z.of_nat in Hx; lia|]);
  assumption. }
split; [intros x Hx1 Hx2; exact (df_bk_trans _ _ _ _ _ _ x (Hgsk x Hx1 Hx2) (KG x Hx1 Hx2))|].
split; [exact (aout_at_kept B RG ly S W m ly' S' W' m' _ _ _ _ _ _ Hout KO (fun b Hb => HIN b (or_intror Hb)))|].
split; [exact Hlive | exact HP'].
Qed.

Lemma df_cutj_journal_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md,
df_cutj_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md ->
AJGXR (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W m md k1.
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md HC.
destruct HC as (e1 & h1 & tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 &
  _ & _ & _ & _ & _ & HMEM & _).
exact (proj1 HMEM).
Qed.

Lemma df_cutj_mem_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md m' md',
df_cutj_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md ->
(forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
AJGXR (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W m' md' k1 ->
df_cutj_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m' md'.
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md m' md' HC Heq HJ'.
pose proof (df_kept_eq W m m' Heq) as KA.
destruct HC as (e1 & h1 & tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) &
  Hpend & Hp0 & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
assert (VK : forall a0 n v0, val_mem SEGS (arm W m) a0 n v0 -> val_mem SEGS (arm W m') a0 n v0)
  by (intros a0 n v0 Hv; apply (akept_vm W m); [intros x _; apply KA | exact Hv]).
pose proof HMEM as (_ & Hrom & _ & _ & _ & _ & _ & _ & Hsrc & _ & _ & _ & _ & Hperm).
assert (HMEM' : DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W m' md' k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1).
{ apply (df_dmem_rebuild_xR cx Hp ly1 S1 Hp1 W m md k1 e1 h1 s1 out1 ev1 _ LB1 ly1 S1 Hp1 W m' md' k1 h1 HMEM HJ');
    try (intros; apply KA); try (intros ? ? ? ?; apply KA).
  - intros a0 Ha0. rewrite (proj1 (KA a0)). exact (Hrom a0 Ha0).
  - intros a0 H1 H2 H3 H4. exact (df_apres_eq (w_H W) m m' a0 Heq H4).
  - reflexivity.
  - apply (asrc_at_kept B ly1 S1 W m ly1 S1 W m' (dHA RG cx) h1 Hsrc); [intros ? ? ? ?; apply KA|].
    intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact Hperm|]. right.
    apply in_or_app. right. apply in_or_app. left. exact Hb.
  - exact Hperm. }
pose proof HMEM' as (_ & _ & _ & _ & HFR' & _).
exists e1, h1, tl, out1, ev1, LB1, spent, jb, a, v, rs, r0, rs0.
exact (conj (conj HFR' (conj (VK _ _ _ M56) (conj (VK _ _ _ M64) (conj (VK _ _ _ M48) (conj (VK _ _ _ M200)
  (conj (VK _ _ _ M32) (conj (VK _ _ _ M24) (conj (VK _ _ _ M72) (conj (VK _ _ _ M80) (conj (VK _ _ _ M40) (VK
  _ _ _ M192))))))))))) (conj Hpend (conj Hp0 (conj Hn0 (conj Hdata (conj HMEM' (conj HnoNUL (conj Hused (conj
  HSAME (conj Hcap (conj Hu (conj Hskip (conj Hkeys (conj Hka (conj Heintr (conj Hpendm (conj Hoff (conj Hstate
  (conj Hen (conj Hecap (conj HHIST (conj HRS (conj HPFUT HBUD))))))))))))))))))))))).
Qed.

Lemma df_cutj_dnum_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md,
df_cutj_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md -> 0 < dnum s1 <= 16384.
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md HC.
destruct HC as (e1 & h1 & tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 &
  _ & _ & _ & Hn0 & _ & HMEM & _ & _ & _ & Hcap & _).
pose proof HMEM as (_ & _ & _ & _ & _ & _ & _ & Hokx & _).
pose proof Hokx as (_ & _ & _ & _ & _ & Hc & _).
split; [exact Hn0|]. revert Hn0 Hcap Hc. clear. intros Hn0 Hcap Hc.
unfold dnum, ulen. rewrite <- Hcap. lia.
Qed.

Lemma df_src_byte_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b,
df_cutjh_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
exists q qn, In (q, qn) (ablocks B ly1 S1) /\ In (q, qn) (asrc_blks h1) /\ q <> hs_partial h1 /\
q <= p0 + Z.of_nat k /\ p0 + Z.of_nat k + 1 <= q + req_size qn /\
val_mem SEGS (arm W m) (p0 + Z.of_nat k) 1 b /\ 0 <= b < 256.
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b HC Hb.
destruct HC as (tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 &
  _ & Hpend & Hp0 & _ & _ & HMEM & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpendm & Hoff & _).
pose proof HMEM as (_ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _ & _ & _ & _ & Hperm).
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Apend & _ & _ & _ & _ & Ahead & _ & _ & _ & _ & _ & _ &
  _ & _ & Anod).
pose proof Apend as (_ & _ & _ & _ & _ & _ & _ & _ & Arecs).
rewrite Hpend in Arecs. apply Forall_inv in Arecs as (Rin & Rg & _ & _).
assert (Hoff0 : 0 <= hs_off h1 < Z.of_nat (length (snd r0))).
{ clear - Ahead Hpend. destruct Ahead as [(Hn & _) | (r & rs' & Hr & Ho)].
  { rewrite Hpend in Hn. discriminate. }
  rewrite Hpend in Hr.
  injection Hr as -> ->. exact Ho. }
unfold ddata, dhead in Hb. rewrite <- Hpendm, Hpend in Hb. cbn [map] in Hb.
apply df_nth_error_firstn in Hb. apply df_nth_error_skipn in Hb.
remember (Z.to_nat (drain_b_c.ds_off s1) + k)%nat as j eqn:Hjdef.
assert (Hj : (j < length (snd r0))%nat).
{ assert (Hne : nth_error (bzs (snd r0)) j <> None) by (rewrite Hb; discriminate).
  apply nth_error_Some in Hne. unfold bzs in Hne. rewrite length_map in Hne. exact Hne. }
assert (Hnth : nth j (bzs (snd r0 ++ [Z_to_bv 8 0])) 0 = b).
{ unfold bzs. rewrite map_app, app_nth1 by (rewrite length_map; exact Hj).
  apply nth_error_nth. exact Hb. }
assert (Hlen : (j < length (bzs (snd r0 ++ [Z_to_bv 8 0])))%nat)
  by (unfold bzs; rewrite length_map, length_app; cbn [length]; clear - Hj; lia).
destruct (Rg j Hlen) as (Hv & Hr). rewrite Hnth in Hv, Hr.
assert (Haddr : fst r0 + Z.of_nat j = p0 + Z.of_nat k)
  by (rewrite Hp0, Hjdef; clear - Hoff Hoff0; lia).
rewrite Haddr in Hv.
exists (fst r0), (Z.of_nat (length (snd r0)) + 1).
split; [exact Rin|].
split.
{ unfold asrc_blks, alist_blks. right. apply in_or_app. left. apply in_or_app. right.
  rewrite Hpend. left. reflexivity. }
split.
{ intros Heq. unfold hs_blocks in Anod. cbn [app] in Anod.
  apply (NoDup_remove_2 _ _ _ (proj1 (NoDup_ListNoDup _) Anod)). apply in_or_app. left.
  unfold list_blocks. apply in_or_app. right. rewrite Hpend. left. exact Heq. }
pose proof (req_size_pos (Z.of_nat (length (snd r0)) + 1) ltac:(clear; lia)) as (_ & Hrq).
split; [rewrite Hp0; clear - Hoff Hoff0; lia|].
split; [rewrite <- Haddr; clear - Hj Hrq; lia|].
split; [exact Hv | exact Hr].
Qed.

Lemma df_entry_full_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W regs m md e1 h1 b,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> (df_regs RG) cx s1 p0 k regs -> Z.of_nat k < dnum s1 ->
df_cutjh_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (df_extra (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b))) df_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_feed)) m (seg_rom SEGS))) /\
sh_ok SEGS df_Bx df_SH (Eimg (Ereg regs (df_extra (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b)))
  (mrestrict (w_H W) m).
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W regs m md e1 h1 b HB HR Hk HC Hb.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HGSB as (HGlo & HGhi & HGal).
pose proof HR as (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
destruct (df_src_byte_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b HC Hb)
  as (q & qn & Hqin & _ & _ & Hq1 & Hq2 & Mb & Hb8).
pose proof (df_cutj_dnum_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md (ex_intro _ e1 (ex_intro _ h1 HC))) as Hn.
destruct HC as (tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) & _ & _ & _ & _ & HMEM & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _).
assert (HAR : ARx ly1 S1 Hp1 W m md) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
pose proof Hsrc as (_ & _ & _ & _ & Aawr & _ & _ & _ & _ & _ & _ & M40' & M48' & M56' & _ & Anp & Aovl & Apb & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W m md q qn HAR Hqin) as (_ & Hq4096 & Hqceil & Hqapp & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W m md _ _ HAR Apb) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos qn (BLKN ly1 S1 Hp1 W m md q qn HAR Hqin)) as (Hrq1 & _).
pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrp).
set (HA := dHA RG cx) in *. set (pk := p0 + Z.of_nat k) in *.
assert (HAe : HA = rg_s RG + ASRC * Z.of_nat (dxj cx)) by reflexivity.
assert (HAlo : rg_s RG <= HA) by (rewrite HAe; unfold ASRC; lia).
assert (HAhi : HA + ASRC <= rg_s RG + 4 * ASRC) by (rewrite HAe; unfold ASRC; lia).
assert (HAal : HA mod 8 = 0).
{ rewrite HAe. unfold ASRC. replace (rg_s RG + 96 * Z.of_nat (dxj cx)) with (rg_s RG + Z.of_nat (dxj cx) * 12 * 8) by lia.
  rewrite Z.mod_add by lia. exact HGal. }
assert (Hdisj : HA + 96 <= pk \/ pk + 1 <= HA).
{ destruct (Z_lt_le_dec pk HA) as [Hlt|Hge]; [right; lia|].
  destruct (Z_lt_le_dec pk (HA + 96)) as [Hlt2|Hge2]; [|left; lia].
  exfalso. apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W m md q qn pk HAR Hqin ltac:(lia)).
  apply (HG pk). unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold ASRC in *. lia. }
assert (Hsp : alloc_ceiling <= spZ regs <= 2 ^ 47) by (rewrite R2; lia).
assert (Hsp16 : spZ regs mod 16 = 0).
{ rewrite R2, HDF. replace (dsp0 cx - 336) with (dsp0 cx + (-21) * 16) by lia. rewrite Z.mod_add by lia.
  exact Hal16. }
split.
- apply ((df_feed_entry RG HGSB) W regs m HA pk (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b (dnum s1) k
    Hsp Hsp16 R21 R23 R19 R25 R24 R26 R20 R27 R22 ltac:(lia) ltac:(unfold ASRC in *; lia) HAal
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold APARTIAL in *; lia) ltac:(destruct Aovl; lia) ltac:(lia)
    ltac:(lia) ltac:(lia) Hdisj).
  + rewrite R2. exact M24.
  + rewrite R2. exact M72.
  + exact M40'.
  + exact M48'.
  + exact M56'.
  + exact Mb.
  + intros i Hi. apply Aawr. unfold ASRC. exact Hi.
- set (E := Eimg (Ereg regs (df_extra (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b))).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
  { intros n r Hn'. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn'. }
  apply (df_feed_shok_x ly1 S1 Hp1 W m md E HA pk q qn HAR).
  + unfold df_Bx. apply U_atom; [rewrite (EE 21%nat 21%bv eq_refl); exact R21 | unfold SHADOW_OFF; lia].
  + apply U_atom; [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia].
  + apply U_atom; [rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia].
  + apply U_atom; [rewrite (EE 26%nat 26%bv eq_refl); exact R26 | lia].
  + exact HAlo.
  + unfold ASRC in *. lia.
  + exact Hqin.
  + exact Hq1.
  + exact Hq2.
  + intros x Hx. revert Hqapp Hq1 Hq2 Hx Hrq1. clear.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.

Lemma df_tail_xR : forall cx Hp kr s1 D k p0 W regs m md Q,
(df_regs RG) cx s1 p0 k regs -> df_cut_xR cx Hp kr s1 D (S k) p0 W m md -> Z.of_nat (S k) <= dnum s1 ->
(forall W2 c2, DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S k) W2 c2 -> SRrG SEGS R W2 c2 Q) ->
(forall W2 c2, DE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W2 c2 -> SRrG SEGS R W2 c2 Q) ->
SRrG SEGS R W (cfg_at SEGS (BASE + A_df_tail) regs m md) Q.
Proof.
intros cx Hp kr s1 D k p0 W regs m md Q HR HC Hle Hnext Hend.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22).
destruct HC as (ly1 & S1 & Hp1 & k1 & HC).
pose proof (df_cutj_journal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as HJ.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HS : st_ok_pi SEGS VAL E df_tss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_df_tail)) m (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold df_tss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint]. exact I.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE 21%nat 21%bv eq_refl), R21. unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
    repeat match goal with |- _ /\ _ => split end; (exact I || lia). }
assert (SHOK : sh_ok SEGS (SOff 21 0) [] E (mrestrict (w_H W) m)) by constructor.
clear HE.
unfold cfg_at.
paj_run_tok_xR RUNR HS HJ SHOK DFspan. { apply awr_ok_x_of0. awr_ok_tac. }
df_meq MEQ1.
pose proof (df_cutj_dnum_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as (Hn0 & Hn16).
assert (E25 : ew E 25 = Z_to_bv 64 (dnum s1 - Z.of_nat k)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (U25 : U E (SOff 25 (-1)) = dnum s1 - Z.of_nat k + -1) by (apply U_atom_off; [exact E25 | lia | lia]).
assert (U0 : U E (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
psrr_branch_tok RUNR BRR HS SHOK DFspan.
- (* the back edge 0x83550 -> 0x8347c: a byte is left *)
  rewrite branch_ne_U, U25, U0 in Hc.
  assert (Hlt : Z.of_nat (S k) < dnum s1)
    by (destruct (Z.eqb_spec (dnum s1 - Z.of_nat k + -1) 0); [discriminate | lia]).
  paj_run_to_tok_xR RUNTOR HS HJ SHOK DFspan A_dr_feed. { apply awr_ok_x_of0. awr_ok_tac. }
  df_meq MEQ2.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (18%bv : bv 5) Q18. prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8.
  prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (19%bv : bv 5) Q19.
  prreg HS (20%bv : bv 5) Q20. prreg HS (27%bv : bv 5) Q27. prreg HS (22%bv : bv 5) Q22.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (24%bv : bv 5) Q24.
  apply Hnext.
  apply (df_DRB_close_xR cx Hp kr s1 D (S k) p0 W).
  + apply ((df_regs_step RG) cx s1 p0 k regs _ HR).
    * rewrite Q2. exact (EE 2%nat 2%bv eq_refl).
    * rewrite Q3. exact (EE 3%nat 3%bv eq_refl).
    * rewrite Q4. exact (EE 4%nat 4%bv eq_refl).
    * rewrite Q18. exact (EE 18%nat 18%bv eq_refl).
    * rewrite Q9. exact (EE 9%nat 9%bv eq_refl).
    * rewrite Q8. exact (EE 8%nat 8%bv eq_refl).
    * rewrite Q21. exact (EE 21%nat 21%bv eq_refl).
    * rewrite Q23. exact (EE 23%nat 23%bv eq_refl).
    * rewrite Q19. exact (EE 19%nat 19%bv eq_refl).
    * rewrite Q20. exact (EE 20%nat 20%bv eq_refl).
    * rewrite Q27. exact (EE 27%nat 27%bv eq_refl).
    * rewrite Q22. exact (EE 22%nat 22%bv eq_refl).
    * rewrite Q25, (EE 25%nat 25%bv eq_refl). reflexivity.
    * rewrite Q26, (EE 26%nat 26%bv eq_refl). reflexivity.
    * rewrite Q24, (EE 24%nat 24%bv eq_refl). reflexivity.
  + exact Hlt.
  + exists ly1, S1, Hp1, k1. apply (df_cutj_mem_xR cx Hp kr s1 D (S k) p0 ly1 S1 Hp1 k1 W m md _ _ HC); [|exact HJ].
    intros x. rewrite MEQ2, MEQ1. reflexivity.
- (* the exit 0x83554 -> 0x835ac: the round's bytes are all fed *)
  rewrite branch_ne_U, U25, U0 in Hc.
  assert (Heq : Z.to_nat (dnum s1) = S k)
    by (destruct (Z.eqb_spec (dnum s1 - Z.of_nat k + -1) 0); [lia | discriminate]).
  paj_run_to_tok_xR RUNTOR HS HJ SHOK DFspan A_dr_fed. { apply awr_ok_x_of0. awr_ok_tac. }
  df_meq MEQ2.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (18%bv : bv 5) Q18. prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8.
  prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (19%bv : bv 5) Q19.
  prreg HS (20%bv : bv 5) Q20. prreg HS (27%bv : bv 5) Q27. prreg HS (22%bv : bv 5) Q22.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (24%bv : bv 5) Q24.
  apply Hend.
  apply (df_DE_close_xR cx Hp kr s1 D (S k) p0 W).
  + apply ((df_regs_step RG) cx s1 p0 k regs _ HR).
    * rewrite Q2. exact (EE 2%nat 2%bv eq_refl).
    * rewrite Q3. exact (EE 3%nat 3%bv eq_refl).
    * rewrite Q4. exact (EE 4%nat 4%bv eq_refl).
    * rewrite Q18. exact (EE 18%nat 18%bv eq_refl).
    * rewrite Q9. exact (EE 9%nat 9%bv eq_refl).
    * rewrite Q8. exact (EE 8%nat 8%bv eq_refl).
    * rewrite Q21. exact (EE 21%nat 21%bv eq_refl).
    * rewrite Q23. exact (EE 23%nat 23%bv eq_refl).
    * rewrite Q19. exact (EE 19%nat 19%bv eq_refl).
    * rewrite Q20. exact (EE 20%nat 20%bv eq_refl).
    * rewrite Q27. exact (EE 27%nat 27%bv eq_refl).
    * rewrite Q22. exact (EE 22%nat 22%bv eq_refl).
    * rewrite Q25, (EE 25%nat 25%bv eq_refl). reflexivity.
    * rewrite Q26, (EE 26%nat 26%bv eq_refl). reflexivity.
    * rewrite Q24, (EE 24%nat 24%bv eq_refl). reflexivity.
  + rewrite Heq. exists ly1, S1, Hp1, k1.
    apply (df_cutj_mem_xR cx Hp kr s1 D (S k) p0 ly1 S1 Hp1 k1 W m md _ _ HC); [|exact HJ].
    intros x. rewrite MEQ2, MEQ1. reflexivity.
Qed.

Lemma df_close_local_xR : forall cx hp kr s1 D k p0 ly1 S1 hp1 k1 W m md e1 h1 m' md' h2 b,
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
df_cutjh_xR cx hp kr s1 D k p0 ly1 S1 hp1 k1 W m md e1 h1 ->
AJGXR (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 hp1 W m' md' k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) ->
   ~ (hs_partial h1 <= a < hs_partial h1 + APARTIAL) -> abyte_kept W m W m' a) ->
(forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_client RG <= a < rg_client RG + 4) \/
   (rg_send_dead RG <= a < rg_send_dead RG + 1) -> abyte_kept W m W m' a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
asrc_at B ly1 S1 W m' (dHA RG cx) h2 ->
nth_error (ddata s1) k = Some b ->
hs_state h2 = fst (step (hs_state h1) b) -> snd (step (hs_state h1) b) = None ->
hs_fd h2 = hs_fd h1 -> hs_open h2 = hs_open h1 -> hs_closed h2 = hs_closed h1 -> hs_eintr h2 = hs_eintr h1 ->
hs_pending h2 = hs_pending h1 -> hs_off h2 = hs_off h1 -> hs_partial h2 = hs_partial h1 ->
hs_expected h2 = hs_expected h1 -> hs_held h2 = hs_held h1 ->
df_cutjh_xR cx hp kr s1 D (S k) p0 ly1 S1 hp1 k1 W m' md' e1 h2.
Proof.
intros cx hp kr s1 D k p0 ly1 S1 hp1 k1 W m md e1 h1 m' md' h2 b HB HC HJ' KP KC Hpres HS2 Hb Hst Hnone
  Efd Eop Ecl Eei Epe Eoff Epa Eex Ehe.
destruct HC as (tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) &
  Hpend & Hp0 & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
pose proof HB as (_ & _ & _ & HGSA & HSAG & _ & _ & _ & Hj & _).
pose proof HMEM as (HJ & Hrom & _ & _ & _ & _ & _ & Hokx & Hsrc & _ & _ & _ & _ & Hperm).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hslo, Hshi.
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H18 & _).
pose proof HGSB as (HGlo & HGhi & _).
pose proof (proj1 (proj1 (@YM05.alloc_ceiling_value rc))) as ACV.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity.
assert (RQP : req_size APARTIAL = APARTIAL) by reflexivity.
assert (RQT : req_size ATABLE = ATABLE) by reflexivity.
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC)
  by (revert Hj; clear; unfold dHA, ASRC; intros; lia).
destruct (alx_blocks _ _ _ LAWS ly1 S1 hp1 W m md (hs_partial h1) APARTIAL HAR H18) as (_ & _ & Hpc & _).
(* image bytes are not in the partial buffer (a heap block) *)
assert (IMP : forall x, in_img SEGS x -> ~ (hs_partial h1 <= x < hs_partial h1 + APARTIAL)).
{ intros x Hi Hp. refine (blk_img_x SEGS B ARx LAWS ly1 S1 hp1 W m md (hs_partial h1) APARTIAL x HAR H18 _ Hi).
  rewrite RQP. exact Hp. }
(* image bytes are addresses *)
assert (IMR : forall x, in_img SEGS x -> 0 <= x < 2 ^ 64).
{ intros x Hi. pose proof (pa_img_range _ Hi) as Hr. revert Hr. clear. intros. lia. }
(* a G_DR byte outside g_s is kept *)
assert (KI : forall x lo n, inG (G_DR B RG) x -> lo <= x < lo + n ->
  (rg_s RG + 4 * ASRC <= lo \/ lo + n <= rg_s RG) -> abyte_kept W m W m' x).
{ intros x lo n Hg Hx Hd. apply KP; [exact (IMR x (proj1 (HG x Hg))) | | exact (IMP x (proj1 (HG x Hg)))].
  revert Hx Hd HAr. clear. unfold ASRC. intros. lia. }
(* the blocks of the cut: the table and the entry's blocks lie before the partial buffer, the out block after *)
pose proof (df_sep_perm_x ly1 S1 hp1 W m md _ HAR Hperm) as Hpw.
assert (DP : forall q, In q ((dxG cx, ATABLE) :: aentry_blks e1) ->
  zdisjoint (block_rng q) (block_rng (hs_partial h1, APARTIAL))).
{ intros q Hq.
  apply (df_pw_app (fun x y => zdisjoint (block_rng x) (block_rng y)) ((dxG cx, ATABLE) :: aentry_blks e1)
    (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) q (hs_partial h1, APARTIAL) Hpw Hq).
  unfold asrc_blks. cbn [app In]. left. reflexivity. }
assert (Hpw2 : pairwise (fun x y => zdisjoint (block_rng x) (block_rng y))
  (((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1) ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx)).
{ rewrite <- app_comm_cons, <- app_assoc. exact Hpw. }
assert (HGin : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
(* the frame [dsp0 - DRAIN_FRAME, dsp0) is above alloc_ceiling, g_s and the heap below it *)
assert (KS : forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W m W m' x).
{ intros x Hx. apply KP.
  - revert Hx Hceil Hslo Hshi H47 ACV. rewrite HDS. clear. unfold DRAIN_FRAME. intros. lia.
  - revert Hx HAr HGhi Hceil Hslo ACV. rewrite HDS. clear. unfold DRAIN_FRAME, ASRC. intros. lia.
  - revert Hx Hpc Hceil Hslo. rewrite RQP, HDS. clear. unfold DRAIN_FRAME. intros. lia. }
(* a byte of a block of the relay entry *)
assert (KB : forall q x, In q (aentry_blks e1) -> fst q <= x < fst q + snd q -> abyte_kept W m W m' x).
{ intros [p n] x Hq Hx. cbn [fst snd] in Hx.
  assert (Hin : In (p, n) (ablocks B ly1 S1)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). right. apply in_or_app. left. exact Hq. }
  pose proof (req_size_pos n (BLKN ly1 S1 hp1 W m md p n HAR Hin)) as (_ & Rn).
  apply KP; [exact (df_blk_rng_x ly1 S1 hp1 W m md p n x HAR Hin Hx) | |].
  - intros Hc. apply (df_blk_gs_x ly1 S1 hp1 W m md p n x HAR Hin Hx). revert Hc HAr. clear. unfold ASRC. intros. lia.
  - intros Hc. pose proof (DP (p, n) (or_intror Hq)) as Dq.
    unfold zdisjoint, block_rng in Dq. cbn [fst snd] in Dq. rewrite RQP in Dq.
    revert Hx Hc Dq Rn. clear. intros. lia. }
(* the memory core at m' *)
assert (HMEM' : DMEM_xR B PST ARx RG R cx hp ly1 S1 hp1 W m' md' k1 e1 h2 s1 out1 ev1 (lines (dSTR cx) D) LB1).
{ apply (df_dmem_rebuild_xR cx hp ly1 S1 hp1 W m md k1 e1 h1 s1 out1 ev1 _ LB1 ly1 S1 hp1 W m' md' k1 h2 HMEM HJ').
  - (* ROM: image, and not in g_s (HGR) *)
    intros x Hx.
    assert (Hi : in_img SEGS x) by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    assert (N1 : ~ (dHA RG cx + 48 <= x < dHA RG cx + 60)).
    { intros Hc. apply (HGR x); [|exact Hx]. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr.
      cbn [fst snd]. revert Hc HAr. clear. unfold ASRC. intros. lia. }
    rewrite (proj1 (KP x (IMR x Hi) N1 (IMP x Hi))). exact (Hrom x Hx).
  - intros x _ _ _ Hx. exact (Hpres x Hx).
  - reflexivity.
  - exact KS.
  - (* the entry's 56 bytes at SA: in the table block *)
    intros x Hx.
    assert (Hxt : dxG cx <= x < dxG cx + ATABLE) by (revert Hx HGSA HSAG; clear; intros; lia).
    apply KP; [exact (df_blk_rng_x ly1 S1 hp1 W m md (dxG cx) ATABLE x HAR HGin Hxt) | |].
    + intros Hc. apply (df_blk_gs_x ly1 S1 hp1 W m md (dxG cx) ATABLE x HAR HGin).
      * revert Hx HGSA HSAG. clear. intros. lia.
      * revert Hc HAr. clear. unfold ASRC. intros. lia.
    + intros Hc. pose proof (DP (dxG cx, ATABLE) (or_introl eq_refl)) as Dq.
      unfold zdisjoint, block_rng in Dq. cbn [fst snd] in Dq. rewrite RQT, RQP in Dq.
      revert Hx Hc Dq HGSA HSAG. clear. intros. lia.
  - (* the entry's blocks *)
    intros r Hr x Hx. pose proof Hokx as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & _).
    unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    + destruct (Z.eqb_spec (re_cap e1) 0) as [Hc0 | Hc0]; cbn [In] in Hr; [destruct Hr|].
      destruct Hr as [<- | []]. unfold gfp in Hx. cbn [fst snd] in Hx. unfold bzs in Hx.
      rewrite length_map, length_app in Hx.
      destruct Hbuf as [(Hc & _) | (Hc & _ & Hjk & _)]; [exfalso; exact (Hc0 Hc)|].
      apply (KB (re_buf e1, re_cap e1)).
      * unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
      * cbn [fst snd]. revert Hx HU Hjk. clear. intros. lia.
    + cbn [In] in Hr. destruct Hr as [<- | Hr].
      * unfold gfp in Hx. cbn [fst snd] in Hx.
        destruct Hhp as [(Hz & Hke) | (Hz & _ & Hk1 & _ & _)].
        -- exfalso. rewrite Hke in Hx. unfold bzs, key_ptrs in Hx. cbn [map concat length] in Hx.
           revert Hx. clear. intros. lia.
        -- unfold bzs in Hx. rewrite length_map, (df_key_ptrs_len RG) in Hx. unfold re_nheld in Hk1.
           apply (KB (re_hp e1, re_kh e1)).
           ++ unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
              rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
           ++ cbn [fst snd]. revert Hx Hk1. clear. intros. lia.
      * apply in_map_iff in Hr as (kk & <- & Hk). unfold gfp in Hx. cbn [fst snd] in Hx.
        unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx.
        apply (KB (key_addr kk, Z.of_nat (length (key_text kk)) + 1)).
        -- unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
           apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
        -- cbn [fst snd]. revert Hx. clear. intros. lia.
  - (* g_s outside slot j: image, outside [HA + 48, HA + 60) *)
    intros x Hx1 Hx2.
    assert (Hgx : inG (G_DR B RG) x)
      by (unfold G_DR, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx1).
    apply KP; [exact (IMR x (proj1 (HG x Hgx))) | | exact (IMP x (proj1 (HG x Hgx)))].
    revert Hx2. clear. unfold ASRC. intros. lia.
  - (* the controller's cells and g_out's block *)
    pose proof HRGD as HR. cbn [zpairwise_disjoint zall_disjoint zdisj fst snd] in HR.
    destruct HR as (_ & _ & (_ & Dcb & Dse & _ & _ & Dno & Dca & Dou & Der & _) & _).
    intros r Hr x Hx. unfold aout_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Hx.
    + exact (KC x (or_introl Hx)).
    + apply (KI x (rg_nout RG) 8); [|exact Hx | exact Dno].
      unfold G_DR, G_SL, inG. do 3 apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + apply (KI x (rg_capout RG) 8); [|exact Hx | exact Dca].
      unfold G_DR, G_SL, inG. do 4 apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + apply (KI x (rg_out RG) 8); [|exact Hx | exact Dou].
      unfold G_DR, G_SL, inG. do 5 apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + exact (KC x (or_intror (or_introl Hx))).
    + apply (KI x (rg_client_broken RG) 1); [|exact Hx | exact Dcb].
      unfold G_DR, G_SL, inG. apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + exact (KC x (or_intror (or_intror Hx))).
    + apply (KI x (rg_send_eintr RG) 1); [|exact Hx | exact Dse].
      unfold G_DR, G_SL, inG. do 2 apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + apply (KI x (as_errno B) 4); [|exact Hx | exact Der].
      unfold G_DR, G_SL, inG. do 6 apply Exists_cons_tl. apply Exists_cons_hd. exact Hx.
    + destruct (drain_b_c.ds_ocap s1 =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|].
      destruct Hr as [<- | []]. cbn [fst snd] in Hx.
      assert (Hq : In (out1, drain_b_c.ds_ocap s1) (aout_blks (drain_b_c.ds_ocap s1) out1))
        by (unfold aout_blks; rewrite Hc0; left; reflexivity).
      assert (Hin : In (out1, drain_b_c.ds_ocap s1) (ablocks B ly1 S1)).
      { apply (Permutation_in _ (Permutation_sym Hperm)). right. apply in_or_app. right.
        apply in_or_app. right. apply in_or_app. left. exact Hq. }
      pose proof (req_size_pos _ (BLKN ly1 S1 hp1 W m md _ _ HAR Hin)) as (_ & Rn).
      apply KP; [exact (df_blk_rng_x ly1 S1 hp1 W m md _ _ x HAR Hin Hx) | |].
      * intros Hc. apply (df_blk_gs_x ly1 S1 hp1 W m md _ _ x HAR Hin Hx). revert Hc HAr. clear. unfold ASRC. intros. lia.
      * intros Hc.
        assert (HPin : In (hs_partial h1, APARTIAL) ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1)).
        { right. apply in_or_app. right. unfold asrc_blks. cbn [In]. left. reflexivity. }
        pose proof (df_pw_app (fun x y => zdisjoint (block_rng x) (block_rng y)) _ _
          (hs_partial h1, APARTIAL) (out1, drain_b_c.ds_ocap s1) Hpw2 HPin (in_or_app _ _ _ (or_introl Hq))) as Dq.
        unfold zdisjoint, block_rng in Dq. cbn [fst snd] in Dq. rewrite RQP in Dq.
        revert Hx Hc Dq Rn. clear. intros. lia.
  - exact HS2.
  - assert (EB : asrc_blks h2 = asrc_blks h1) by (unfold asrc_blks; rewrite Epa, Epe, Eex, Ehe; reflexivity).
    rewrite EB. exact Hperm. }
pose proof HMEM' as (_ & _ & _ & _ & HFR' & _).
assert (VK : forall a0 n v0, val_mem SEGS (arm W m) a0 n v0 -> dsp0 cx - DRAIN_FRAME <= a0 ->
  a0 + Z.of_nat n <= dsp0 cx -> val_mem SEGS (arm W m') a0 n v0).
{ intros a0 n v0 Hv H1 H2. apply (akept_vm W m); [|exact Hv]. intros x Hx. apply KS. lia. }
(* the model: the byte pushes no line, so the lines so far and the lines to come are the same *)
pose proof HHIST as (_ & HRef & _).
assert (LS : lines (drain_b_c.ds_ref s1) (firstn (S k) (ddata s1)) =
  lines (drain_b_c.ds_ref s1) (firstn k (ddata s1))).
{ rewrite (df_firstn_nth_app _ _ _ Hb), df_lines_snoc, <- Hstate, Hnone. exact (app_nil_r _). }
assert (LF : lines (dSTR cx) (D ++ firstn (S k) (ddata s1)) = lines (dSTR cx) (D ++ firstn k (ddata s1))).
{ rewrite (df_firstn_nth_app _ _ _ Hb), app_assoc, df_lines_snoc, feed_app, <- HRef, <- Hstate, Hnone.
  exact (app_nil_r _). }
assert (LR : lines (feed (drain_b_c.ds_ref s1) (firstn (S k) (ddata s1))) (skipn (S k) (ddata s1)) =
  lines (feed (drain_b_c.ds_ref s1) (firstn k (ddata s1))) (skipn k (ddata s1))).
{ rewrite (df_skipn_nth _ _ _ Hb), (df_firstn_nth_app _ _ _ Hb), df_feed_snoc, <- Hstate.
  change (b :: skipn (S k) (ddata s1)) with ([b] ++ skipn (S k) (ddata s1)).
  rewrite lines_app, df_lines_one, df_feed_one, Hnone. reflexivity. }
exists tl, out1, ev1, LB1, spent, jb, a, v, rs, r0, rs0.
split.
{ unfold df_slots. split; [exact HFR'|].
  split; [apply (VK _ _ _ M56); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M64); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M48); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M200); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M32); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M24); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M72); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M80); unfold DRAIN_FRAME; clear; lia|].
  split; [apply (VK _ _ _ M40); unfold DRAIN_FRAME; clear; lia|].
  apply (VK _ _ _ M192); unfold DRAIN_FRAME; clear; lia. }
split; [rewrite Epe; exact Hpend|].
split; [exact Hp0|]. split; [exact Hn0|]. split; [exact Hdata|]. split; [exact HMEM'|].
split; [exact HnoNUL|]. split; [exact Hused|].
split; [unfold DSAME in HSAME |- *; rewrite Efd, Eop, Ecl, Epe, Epa, Ehe; exact HSAME|].
split; [exact Hcap|]. split; [exact Hu|]. split; [exact Hskip|]. split; [exact Hkeys|]. split; [exact Hka|].
split; [rewrite Eei; exact Heintr|].
split; [rewrite Epe; exact Hpendm|].
split; [rewrite Eoff; exact Hoff|].
split; [rewrite Hst, (df_firstn_nth_app _ _ _ Hb), df_feed_snoc, <- Hstate; reflexivity|].
split; [rewrite Eex, LS; exact Hen|].
split; [rewrite Eex, LS; exact Hecap|].
split; [unfold DHIST in HHIST |- *; rewrite Eex, LF; exact HHIST|].
split; [exact HRS|].
split; [unfold dpfut in HPFUT |- *; cbv zeta in HPFUT |- *; rewrite LR, LS; exact HPFUT|].
exact HBUD.
Qed.

Lemma df_close_push_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl ly2 S2 Hp2 k2 W2 m2 md2 l2 d,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
df_cutjt_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl ->
nth_error (ddata s1) k = Some 0 -> hs_overlong h1 = 0 ->
AJGXR (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 k2 ->
(forall p n i, In (p, n) (ablocks B ly1 S1) -> p <> hl_v (hs_expected h1) -> 0 <= i < req_size n ->
   abyte_kept W m W2 m2 (p + i)) ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   ~ Exists (in_zr a) PST ->
   ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) -> ~ (dHA RG cx + 64 <= a < dHA RG cx + 80) ->
   abyte_kept W m W2 m2 a) ->
(forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_client RG <= a < rg_client RG + 4) \/
   (rg_send_dead RG <= a < rg_send_dead RG + 1) \/ (as_errno B <= a < as_errno B + 4) ->
   abyte_kept W m W2 m2 a) ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W2 m2 a) ->
rom_view SEGS W2 m2 -> apres_kept B W m W2 m2 -> frames S2 = frames S1 ->
alist_at B ly2 S2 W2 m2 (dHA RG cx + 64) l2 true ->
val_mem SEGS (arm W2 m2) (dHA RG cx + 48) 8 0 -> val_mem SEGS (arm W2 m2) (dHA RG cx + 56) 4 0 ->
hl_recs l2 = hl_recs (hs_expected h1) ++ [(d, hs_W h1)] ->
hl_cap l2 = ListRep.grow_cap (hl_n (hs_expected h1)) (hl_cap (hs_expected h1)) ->
(lp_grow (hs_expected h1) = false -> hl_v l2 = hl_v (hs_expected h1)) ->
(forall rest,
 Permutation (ablocks B ly1 S1)
   ((if lp_grow (hs_expected h1) && negb (hl_cap (hs_expected h1) =? 0)
     then [(hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))] else []) ++ rest) ->
 Permutation (ablocks B ly2 S2)
   ((d, Z.of_nat (length (hs_W h1)) + 1) ::
    (if lp_grow (hs_expected h1) then [(hl_v l2, AREC * hl_cap l2)] else []) ++ rest)) ->
mo_le MT S1 S2 (lp_cost MT (hs_expected h1) (Z.of_nat (length (hs_W h1)))) ->
rp_RM RP S2 (df_kr2 (hs_expected h1) (Z.of_nat (length (hs_W h1))) tl kr) ->
df_cutjh_xR cx Hp kr s1 D (S k) p0 ly2 S2 Hp2 k2 W2 m2 md2 e1
  (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
      (hs_pjunk h1) 0 0 (hs_pad h1) l2 (hs_held h1)).
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl ly2 S2 Hp2 k2 W2 m2 md2 l2 d HB HC Hnth Hov HJ2 Hbk Hik
  Hcell Hfr Hrom2 Hpres2 Hfrm2 Hl2 Hnp2 Hov2 Hrecs2 Hcap2 Hv2 HLP Hmle2 HRM2.
match goal with |- df_cutjh_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?H => set (h2 := H) end.
destruct HC as (out1 & ev1 & LB1 & spent & jb & ad & v0 & rs & r0 & rs0 &
  (HFR & M56 & M64 & M48 & M200 & M32 & M24 & M72 & M80 & M40 & M192) &
  Hpend & Hp0 & Hn0 & Hdata & HMEM & HnoNUL & Hused & HSAME & Hcap & Hu & Hskip & Hkeys & Hka & Heintr &
  Hpendm & Hoff & Hstate & Hen & Hecap & HHIST & HRS & HPFUT & HBUD).
pose proof HMEM as (HJ & Hrom & Hpres & Hfrs & HFRd & Hent & Hawr & Hokx & Hsrc & Hoth & Hgsk & Hout & Hlive & Hperm).
pose proof Hsrc as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & H24).
destruct HB as (_ & _ & _ & HSAlo & HSAhi & _ & _ & _ & Hj & _).
assert (HAR1 : ARx ly1 S1 Hp1 W m md) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
assert (HHA : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC)
  by (revert Hj; clear; intros Hj; unfold dHA, ASRC; lia).
pose proof H22 as (_ & _ & _ & _ & Hncap & Hvdisj & _).
assert (HC0 : 0 <= hl_cap (hs_expected h1)) by (clear - Hncap; unfold hl_n in Hncap; lia).
(* ---- the blocks: the cut's list with the expected list's vector OV in front of the rest R0 ---- *)
pose (RECS := map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs (hs_expected h1))).
pose (OV := if hl_cap (hs_expected h1) =? 0 then []
  else [(hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))]).
pose (OV2 := if hl_cap l2 =? 0 then [] else [(hl_v l2, AREC * hl_cap l2)]).
pose (R0 := (dxG cx, ATABLE) :: aentry_blks e1 ++ ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ RECS ++
  alist_blks (hs_held h1)) ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx).
assert (P0 : Permutation (ablocks B ly1 S1) (OV ++ R0)).
{ change (asrc_blks h1) with ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ (OV ++ RECS) ++
    alist_blks (hs_held h1)) in Hperm.
  eapply Permutation_trans; [exact Hperm|]. unfold R0. apply df_pu_perm_old. }
assert (IN0 : forall b, In b R0 -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym P0)); apply in_or_app; right; exact Hb).
assert (NV : forall p n, In (p, n) R0 -> p <> hl_v (hs_expected h1)).
{ intros p n Hin. destruct Hvdisj as [(Hc0 & Hv0) | (Hcp & _)].
  - rewrite Hv0. destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W m md p n HAR1 (IN0 _ Hin)) as (_ & H4096 & _).
    clear - H4096. lia.
  - assert (P0' : Permutation (ablocks B ly1 S1)
      ((hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1)) :: R0)).
    { unfold OV in P0. rewrite (proj2 (Z.eqb_neq (hl_cap (hs_expected h1)) 0) ltac:(clear - Hcp; lia)) in P0.
      exact P0. }
    intros Heq. exact (df_pu_ne_in_x ly1 S1 Hp1 W m md _ (p, n) R0 HAR1 P0' Hin (eq_sym Heq)). }
assert (KB : forall p n x, In (p, n) R0 -> p <= x < p + req_size n -> abyte_kept W m W2 m2 x).
{ intros p n x Hin Hx.
  pose proof (Hbk p n (x - p) (IN0 _ Hin) (NV p n Hin) ltac:(clear - Hx; lia)) as Hk.
  replace (p + (x - p)) with x in Hk by ring. exact Hk. }
(* ---- the image bytes the call keeps ---- *)
assert (IKs : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx + 48 <= x < dHA RG cx + 60) ->
  ~ (dHA RG cx + 64 <= x < dHA RG cx + 80) -> abyte_kept W m W2 m2 x).
{ intros x Hx Q1 Q2. destruct ((df_pu_gs B RG HRGD) x Hx) as (HinG & Hne). destruct (HG x HinG) as (Him & Hno & _).
  exact (Hik x Him Hno Hne (PSTG x Hx) Q1 Q2). }
assert (IKj : forall x, dHA RG cx <= x < dHA RG cx + ASRC -> ~ (dHA RG cx + 48 <= x < dHA RG cx + 60) ->
  ~ (dHA RG cx + 64 <= x < dHA RG cx + 80) -> abyte_kept W m W2 m2 x).
{ intros x Hx Q1 Q2. apply IKs; [clear - Hx HHA; lia | exact Q1 | exact Q2]. }
assert (IKo : forall x, (rg_client_broken RG <= x < rg_client_broken RG + 1 \/
  rg_send_eintr RG <= x < rg_send_eintr RG + 1 \/ rg_nout RG <= x < rg_nout RG + 8 \/
  rg_capout RG <= x < rg_capout RG + 8 \/ rg_out RG <= x < rg_out RG + 8) -> abyte_kept W m W2 m2 x).
{ intros x Hx. destruct ((df_pu_sl B RG HRGD) x Hx) as (HinG & Hne & Hngs). destruct (HG x HinG) as (Him & Hno & _).
  assert (HSL : inG (G_SL B RG) x)
    by (unfold G_SL, inG; destruct Hx as [Q|[Q|[Q|[Q|Q]]]];
        repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Q | apply Exists_cons_tl])).
  apply (Hik x Him Hno Hne (PSTO x (or_introl HSL))); intros Hc; apply Hngs; destruct HHA as [Q1 Q2];
  unfold ASRC in Q1, Q2 |- *; clear - Hc Q1 Q2; lia. }
(* h->npartial and h->overlong: written by the two stores, writable because present and not hidden *)
assert (WR : forall x, dHA RG cx + 48 <= x < dHA RG cx + 60 -> writable_at SEGS (arm W2 m2) x).
{ intros x Hx.
  assert (Hxs : rg_s RG <= x < rg_s RG + 4 * ASRC)
    by (destruct HHA as [Q1 Q2]; unfold ASRC in Q1, Q2 |- *; clear - Hx Q1 Q2; lia).
  destruct ((df_pu_gs B RG HRGD) x Hxs) as (HinG & Hne). destruct (HG x HinG) as (Him & Hno & _).
  unfold arm. apply (df_pu_wr (w_H W) (w_H W2) m m2 x).
  - apply (hidden_not_img SEGS). rewrite unsigned_lit_small by (pose proof HGSB as HGB; clear - Hxs HGB; lia).
    exact Him.
  - exact (Hpres2 x Him Hno Hne).
  - pose proof (H5 (x - dHA RG cx) ltac:(clear - Hx; unfold ASRC; lia)) as Hw.
    replace (dHA RG cx + (x - dHA RG cx)) with x in Hw by ring. exact Hw. }
(* ---- the blocks after the push ---- *)
assert (NP0 : Permutation (ablocks B ly2 S2) ((d, Z.of_nat (length (hs_W h1)) + 1) :: OV2 ++ R0)).
{ destruct (lp_grow (hs_expected h1)) eqn:EG; rewrite ?EG in HLP.
  - assert (Hnz : hl_cap l2 <> 0).
    { rewrite Hcap2. unfold lp_grow in EG. apply Z.eqb_eq in EG. unfold ListRep.grow_cap. rewrite EG, Z.eqb_refl.
      clear - HC0. destruct (Z.eqb_spec (hl_cap (hs_expected h1)) 0); cbv iota; lia. }
    assert (Hpre : Permutation (ablocks B ly1 S1) ((if true && negb (hl_cap (hs_expected h1) =? 0)
      then [(hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))] else []) ++ R0)).
    { revert P0. unfold OV. destruct (hl_cap (hs_expected h1) =? 0); intros P0; exact P0. }
    pose proof (HLP R0 Hpre) as HQ. unfold OV2. rewrite (proj2 (Z.eqb_neq (hl_cap l2) 0) Hnz). exact HQ.
  - assert (Hpre : Permutation (ablocks B ly1 S1) ((if false && negb (hl_cap (hs_expected h1) =? 0)
      then [(hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))] else []) ++ (OV ++ R0))) by exact P0.
    pose proof (HLP (OV ++ R0) Hpre) as HQ.
    assert (EOV : OV2 = OV).
    { unfold OV2, OV. rewrite Hcap2, (Hv2 eq_refl). unfold lp_grow in EG. unfold ListRep.grow_cap. rewrite EG.
      reflexivity. }
    rewrite EOV. exact HQ. }
assert (NP : Permutation (ablocks B ly2 S2)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h2 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx)).
{ eapply Permutation_trans; [exact NP0|].
  change (asrc_blks h2) with ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ alist_blks l2 ++
    alist_blks (hs_held h1)).
  assert (EL2 : alist_blks l2 = OV2 ++ RECS ++ [(d, Z.of_nat (length (hs_W h1)) + 1)])
    by (unfold alist_blks; rewrite Hrecs2, map_app; reflexivity).
  rewrite EL2. unfold R0. apply df_pu_perm_new. }
assert (IN2 : forall b, In b ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ alist_blks l2 ++
  alist_blks (hs_held h1)) -> In b (ablocks B ly2 S2)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym NP)). right. apply in_or_app. right. apply in_or_app. left.
  exact Hb. }
(* ---- the harness source after the push ---- *)
assert (HS2 : asrc_at B ly2 S2 W2 m2 (dHA RG cx) h2).
{ unfold asrc_at, h2.
  cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
    hs_expected hs_held].
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H1]|].
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H2]|].
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H3]|].
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H4]|].
  split.
  { intros i Hi.
    assert (Hcase : (48 <= i < 60) \/ (64 <= i < 80) \/ (~ (48 <= i < 60) /\ ~ (64 <= i < 80))) by (clear; lia).
    destruct Hcase as [Q|[Q|[Q1 Q2]]].
    - apply WR. clear - Q. lia.
    - pose proof Hl2 as (_ & _ & _ & Hl2w & _). pose proof (Hl2w (i - 64) ltac:(clear - Q; lia)) as Hw.
      replace (dHA RG cx + 64 + (i - 64)) with (dHA RG cx + i) in Hw by ring. exact Hw.
    - apply (proj2 (IKj (dHA RG cx + i) ltac:(clear - Hi; lia) ltac:(clear - Q1; lia) ltac:(clear - Q2; lia))).
      exact (H5 i Hi). }
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split.
  { apply (alist_at_kept B ly1 S1 W m ly2 S2 W2 m2 (dHA RG cx + 16) (hs_pending h1) false H10).
    - apply ((df_pu_alist_kept B RG) ly1 S1 W W2 m m2 (dHA RG cx + 16) (hs_pending h1) false H10).
      + intros x Hx. apply IKj; clear - Hx; unfold ASRC; lia.
      + intros p n x Hin Hx. apply (KB p n x); [unfold R0; df_pu_in | exact Hx].
    - intros b Hb. apply IN2. right. apply in_or_app. left. exact Hb. }
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H11]|].
  split; [apply (akept_vm W m); [intros x Hx; apply IKj; simpl Z.of_nat in Hx; clear - Hx; unfold ASRC; lia
    | exact H12]|].
  split; [exact Hnp2|]. split; [exact Hov2|]. split; [exact H15|].
  split; [clear; unfold APARTIAL; lia|]. split; [left; reflexivity|].
  split; [apply IN2; left; reflexivity|]. split; [exact H19|].
  split.
  { apply (akept_garr8 W m); [|exact H20]. intros x Hx.
    apply (KB (hs_partial h1) APARTIAL x); [unfold R0; df_pu_in|].
    unfold bzs in Hx. rewrite length_map, H19 in Hx. change (req_size APARTIAL) with 6000.
    clear - Hx. unfold APARTIAL in *. lia. }
  split; [intros Hc; exact Hc|].
  split; [exact Hl2|].
  split.
  { apply (alist_at_kept B ly1 S1 W m ly2 S2 W2 m2 (dHA RG cx + 80) (hs_held h1) true H23).
    - apply ((df_pu_alist_kept B RG) ly1 S1 W W2 m m2 (dHA RG cx + 80) (hs_held h1) true H23).
      + intros x Hx. apply IKj; clear - Hx; unfold ASRC; lia.
      + intros p n x Hin Hx. apply (KB p n x); [unfold R0; df_pu_in | exact Hx].
    - intros b Hb. apply IN2. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  assert (ND : List.NoDup (map fst ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ alist_blks l2 ++
    alist_blks (hs_held h1)))).
  { apply (df_pu_nd_x ly2 S2 Hp2 W2 m2 md2 _ ((dxG cx, ATABLE) :: aentry_blks e1)
      (aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) HAR2). exact NP. }
  cbn [map fst] in ND. rewrite !map_app, !df_pu_lb in ND.
  unfold hs_blocks. cbn [hs_pending hs_partial hs_expected hs_held].
  apply NoDup_ListNoDup. exact (Permutation_NoDup (Permutation_middle _ _ _) ND). }
(* ---- DMEM after the push ---- *)
assert (KA : forall x, dxSA cx <= x < dxSA cx + AENT -> abyte_kept W m W2 m2 x).
{ intros x Hx. apply (KB (dxG cx) ATABLE x); [unfold R0; left; reflexivity|].
  change (req_size ATABLE) with 896. clear - Hx HSAlo HSAhi. unfold AENT, ATABLE in *. lia. }
assert (KE : akept W m W2 m2 (aentry_fp e1)).
{ apply ((df_pu_aentry_kept B RG) ly1 S1 W W2 m m2 e1 Hokx). intros p n x Hin Hx.
  apply (KB p n x); [unfold R0; df_pu_in | exact Hx]. }
assert (KG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
  abyte_kept W m W2 m2 x).
{ intros x Hx1 Hx2. apply IKs; [exact Hx1 | intros Hc; apply Hx2; clear - Hc; unfold ASRC; lia
  | intros Hc; apply Hx2; clear - Hc; unfold ASRC; lia]. }
assert (KO : akept W m W2 m2 (aout_fp B RG (drain_b_c.ds_ocap s1) out1)).
{ intros r Hr x Hx. unfold aout_fp in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd] in Hx.
  - apply Hcell. left. exact Hx.
  - apply IKo. right; right; left. exact Hx.
  - apply IKo. right; right; right; left. exact Hx.
  - apply IKo. right; right; right; right. exact Hx.
  - apply Hcell. right; left. exact Hx.
  - apply IKo. left. exact Hx.
  - apply Hcell. right; right; left. exact Hx.
  - apply IKo. right; left. exact Hx.
  - apply Hcell. right; right; right. exact Hx.
  - revert Hr. destruct (Z.eqb_spec (drain_b_c.ds_ocap s1) 0) as [E0|E0]; intros Hr; [destruct Hr|].
    destruct Hr as [<-|[]]. cbn [fst snd] in Hx.
    assert (Hin : In (out1, drain_b_c.ds_ocap s1) R0).
    { unfold R0, aout_blks. rewrite (proj2 (Z.eqb_neq _ _) E0). df_pu_in. }
    pose proof (req_size_pos (drain_b_c.ds_ocap s1) (BLKN ly1 S1 Hp1 W m md _ _ HAR1 (IN0 _ Hin))) as (_ & Hrq).
    apply (KB _ _ x Hin). clear - Hx Hrq. lia. }
assert (HMEM2 : DMEM_xR B PST ARx RG R cx Hp ly2 S2 Hp2 W2 m2 md2 k2 e1 h2 s1 out1 ev1 (lines (dSTR cx) D) LB1)
  by exact (df_dmem_rebuild_xR cx Hp ly1 S1 Hp1 W m md k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 ly2 S2 Hp2 W2 m2
    md2 k2 h2 HMEM HJ2 Hrom2 Hpres2 Hfrm2 Hfr KA KE KG KO HS2 NP).
pose proof HMEM2 as (_ & _ & _ & _ & HFR2 & _).
assert (VK : forall a0 n v, dsp0 cx - DRAIN_FRAME <= a0 -> a0 + Z.of_nat n <= dsp0 cx ->
  val_mem SEGS (arm W m) a0 n v -> val_mem SEGS (arm W2 m2) a0 n v).
{ intros a0 n v Q1 Q2 Hv. apply (akept_vm W m); [intros x Hx; apply Hfr; clear - Q1 Q2 Hx; lia | exact Hv]. }
assert (SL2 : (df_slots RG) cx W2 m2).
{ unfold df_slots. split; [exact HFR2|].
  repeat (split; [apply VK; [unfold DRAIN_FRAME; clear; lia | unfold DRAIN_FRAME; simpl Z.of_nat; clear; lia
    | assumption]|]).
  apply VK; [unfold DRAIN_FRAME; clear; lia | unfold DRAIN_FRAME; simpl Z.of_nat; clear; lia | assumption]. }
(* ---- the splitter: the NUL byte pushes the partial line and resets the state ---- *)
pose proof (df_step_push h1 Hov) as STP.
pose proof (df_firstn_nth_app (ddata s1) k 0 Hnth) as HFS.
assert (FEED1 : feed (drain_b_c.ds_ref s1) (firstn (S k) (ddata s1)) = LS [] false).
{ rewrite HFS, df_feed_snoc, <- Hstate, STP. reflexivity. }
assert (LINES1 : lines (drain_b_c.ds_ref s1) (firstn (S k) (ddata s1)) =
  lines (drain_b_c.ds_ref s1) (firstn k (ddata s1)) ++ [bzs (hs_W h1)]).
{ rewrite HFS, df_lines_snoc, <- Hstate, STP. reflexivity. }
assert (NE : hl_n l2 = hl_n (hs_expected h1) + 1)
  by (unfold hl_n; rewrite Hrecs2, length_app; cbn [length]; clear; lia).
unfold DHIST in HHIST. destruct HHIST as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11).
assert (LD : lines (dSTR cx) (D ++ firstn (S k) (ddata s1)) =
  lines (dSTR cx) (D ++ firstn k (ddata s1)) ++ [bzs (hs_W h1)]).
{ rewrite HFS, app_assoc, df_lines_snoc, feed_app, <- Y2, <- Hstate, STP. reflexivity. }
assert (HH2 : DHIST cx s1 D (D ++ firstn (S k) (ddata s1)) (lines (dSTR cx) D) (lines (dSTR cx) D) h2 LB1 0).
{ unfold DHIST. change (hs_expected h2) with l2.
  pose proof (f_equal (@length _) Y3) as YL. rewrite length_app, !length_map in YL.
  refine (conj Y1 (conj Y2 (conj _ (conj _ (conj _ (conj Y6 (conj Y7 (conj Y8 (conj Y9 (conj Y10 Y11)))))))))).
  - rewrite Hrecs2, map_app, Y3, LD, map_app, <- app_assoc. cbn [map snd]. rewrite df_pu_bzs_inv. reflexivity.
  - rewrite Hrecs2, firstn_app.
    replace (length (hl_recs (hs_expected (dxh cx))) - length (hl_recs (hs_expected h1)))%nat with 0%nat
      by (clear - YL; lia).
    rewrite firstn_O, app_nil_r. exact Y4.
  - rewrite Hcap2, NE. revert Y5 Hncap. clear. unfold hl_n. intros Y5 Hncap. unfold ListRep.grow_cap.
    destruct (Z.eqb_spec (Z.of_nat (length (hl_recs (hs_expected h1)))) (hl_cap (hs_expected h1)));
    [destruct (Z.eqb_spec (hl_cap (hs_expected h1)) 0)|]; cbv iota; lia. }
(* ---- the pushes still to come: the first is this one ---- *)
unfold dpfut in HPFUT. cbv zeta in HPFUT.
rewrite (df_pu_skipn_cons (ddata s1) k 0 Hnth), lines_cons, <- Hstate, STP in HPFUT.
cbn [drain_b_c.pushes_run fst snd] in HPFUT.
destruct HPFUT as (tl2 & HDR & Htl).
rewrite RelayRunT.nret_app, Nat.add_assoc in HDR.
destruct HBUD as (HBUD & _ & HCNT1).
subst tl. rewrite <- app_assoc in HBUD, HCNT1, HRM2.
(* ---- the meter ---- *)
assert (BOV : bsum OV = AREC * hl_cap (hs_expected h1)).
{ unfold OV. destruct (Z.eqb_spec (hl_cap (hs_expected h1)) 0) as [E|E]; unfold bsum; cbn [fold_right snd];
  clear - E; unfold AREC; lia. }
assert (BOV2 : bsum OV2 = AREC * hl_cap l2).
{ unfold OV2. destruct (Z.eqb_spec (hl_cap l2) 0) as [E|E]; unfold bsum; cbn [fold_right snd];
  clear - E; unfold AREC; lia. }
assert (BB1 : blocks_bytes S1 = bsum R0 + AREC * hl_cap (hs_expected h1)).
{ rewrite (blocks_bytes_bsum B ly1 S1), (bsum_perm _ _ P0), bsum_app, BOV. clear; lia. }
assert (BB2 : blocks_bytes S2 = bsum R0 + AREC * ListRep.grow_cap (hl_n (hs_expected h1)) (hl_cap (hs_expected h1)) +
  (Z.of_nat (length (hs_W h1)) + 1)).
{ rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ NP0), bsum_cons, bsum_app, BOV2, Hcap2. cbn [snd].
  clear; lia. }
(* ---- the counts: the vector the push leaves (OV2) against the one it found (OV) ---- *)
assert (EOV2 : OV2 = (if hl_n (hs_expected h1) =? hl_cap (hs_expected h1)
  then [(hl_v l2, AREC * ListRep.grow_cap (hl_n (hs_expected h1)) (hl_cap (hs_expected h1)))] else OV)).
{ unfold OV2. rewrite Hcap2. destruct (Z.eqb_spec (hl_n (hs_expected h1)) (hl_cap (hs_expected h1))) as [E|E].
  - assert (Hnz : ListRep.grow_cap (hl_n (hs_expected h1)) (hl_cap (hs_expected h1)) <> 0).
    { unfold ListRep.grow_cap. rewrite E, Z.eqb_refl. clear - HC0.
      destruct (Z.eqb_spec (hl_cap (hs_expected h1)) 0); cbv iota; lia. }
    rewrite (proj2 (Z.eqb_neq _ 0) Hnz). reflexivity.
  - unfold OV. rewrite (Hv2 ltac:(unfold lp_grow; apply Z.eqb_neq; exact E)).
    unfold ListRep.grow_cap. rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity. }
(* ---- the cut at S k ---- *)
lazymatch type of HDR with
| context [dapush _ (snd (drain_b_c.pushes_run ?N1 ?C1 ?L1 ?J1 ?V1 ?RS1))] =>
  exists (fst (fst (drain_b_c.pushes_run N1 C1 L1 J1 V1 RS1)) ++ tl2), out1, ev1, LB1,
    (spent + lp_cost MT (hs_expected h1) (Z.of_nat (length (hs_W h1)))), J1, ad, V1, RS1, r0, rs0
end.
refine (conj SL2 (conj Hpend (conj Hp0 (conj Hn0 (conj Hdata (conj HMEM2 (conj HnoNUL (conj Hused (conj HSAME
  (conj Hcap (conj Hu (conj Hskip (conj Hkeys (conj Hka (conj Heintr (conj Hpendm (conj Hoff (conj _ (conj _
  (conj _ (conj HH2 (conj HRS (conj _ _))))))))))))))))))))))).
- rewrite FEED1. reflexivity.
- change (hs_expected h2) with l2. rewrite NE, Hen, LINES1, length_app. cbn [length]. clear; lia.
- change (hs_expected h2) with l2. rewrite Hcap2, LINES1, (df_pu_pcapm_snoc RG), Hen, Hecap. apply (df_pu_grow_push RG).
- unfold dpfut. cbv zeta. rewrite LINES1, FEED1, (df_pu_pcapm_snoc RG), (df_pu_len_snoc RG).
  exists tl2. split; [exact HDR | reflexivity].
- unfold dbud_x. refine (conj _ (conj _ _)).
  + eapply ((df_pu_bud MT MMAX RG MTL HGSB) cx S1 S2 spent (hs_expected h1)); [exact HBUD | exact Hen | exact Hecap
      | unfold bzs; rewrite length_map; reflexivity | clear; lia | rewrite <- Hecap; exact HC0
      | exact Hmle2 | exact BB1 | exact BB2].
  + (* the room: list_push's post at the budget it was given, the room of the requests after it *)
    erewrite df_kr2_eq in HRM2; [exact HRM2 | exact Hen | exact Hecap | unfold bzs; rewrite length_map; reflexivity].
  + (* the counts: list_push's requests change them by their net count *)
    refine (df_pu_cnt _ _ _ _ _ _ _ _ _ OV OV2 R0 _ (hl_v l2) Hen Hecap _ P0 NP0 _ _ HCNT1);
    first [unfold bzs; rewrite length_map; reflexivity | unfold OV; rewrite Hecap; reflexivity
      | rewrite EOV2, Hen, Hecap; reflexivity].
Qed.

Lemma df_cutjh_journal_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1,
df_cutjh_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 ->
AJGXR (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W m md k1.
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 HC.
exact (df_cutj_journal_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md (ex_intro _ e1 (ex_intro _ h1 HC))).
Qed.

Lemma df_finish_nw_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b regs' m' md' np2 ovl2 Q,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> (df_regs RG) cx s1 p0 k regs' -> Z.of_nat k < dnum s1 ->
df_cutjh_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
AJGXR (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W m' md' k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) -> abyte_kept W m W m' a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
val_mem SEGS (arm W m') (dHA RG cx + 48) 8 np2 -> val_mem SEGS (arm W m') (dHA RG cx + 56) 4 ovl2 ->
0 <= np2 <= APARTIAL -> (ovl2 = 0 \/ ovl2 = 1) ->
hs_state (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
  (hs_pjunk h1) np2 ovl2 (hs_pad h1) (hs_expected h1) (hs_held h1)) = fst (step (hs_state h1) b) ->
snd (step (hs_state h1) b) = None ->
~ In (Z_to_bv 8 0) (firstn (Z.to_nat np2) (hs_pjunk h1)) ->
(forall W2 c2, DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S k) W2 c2 -> SRrG SEGS R W2 c2 Q) ->
(forall W2 c2, DE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W2 c2 -> SRrG SEGS R W2 c2 Q) ->
SRrG SEGS R W (cfg_at SEGS (BASE + A_df_tail) regs' m' md') Q.
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b regs' m' md' np2 ovl2 Q HB HR' Hk HC Hb HJ' KEEP PR
  V48 V56 Hnp2 Hov2 Hst Hnone HW0 Hnext Hend.
set (h2 := HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
  (hs_pjunk h1) np2 ovl2 (hs_pad h1) (hs_expected h1) (hs_held h1)) in *.
pose proof HGSB as (HGlo & HGhi & HGal).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
pose proof HC as HC0.
destruct HC as (tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 & _ & _ & _ & _ & _ & HMEM & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _).
assert (HAR : ARx ly1 S1 Hp1 W m md) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Apb & Apj & Apg & _).
assert (HAe : dHA RG cx = rg_s RG + ASRC * Z.of_nat (dxj cx)) by reflexivity.
assert (HAlo : rg_s RG <= dHA RG cx) by (rewrite HAe; unfold ASRC; lia).
assert (HAhi : dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (rewrite HAe; unfold ASRC in *; lia).
assert (Hsrc2 : asrc_at B ly1 S1 W m' (dHA RG cx) h2).
{ apply (df_asrc_upd_x ly1 S1 Hp1 W m md m' (dHA RG cx) h1 h2 HAR Hsrc HAlo HAhi).
  - intros x Hx H1 _. exact (KEEP x Hx H1).
  - exact PR.
  - exact V48.
  - exact V56.
  - exact Hnp2.
  - exact Hov2.
  - exact Apj.
  - apply (akept_garr8 W m); [|exact Apg]. intros x Hx.
    unfold bzs in Hx. rewrite length_map in Hx. change (hs_pjunk h2) with (hs_pjunk h1) in Hx. rewrite Apj in Hx.
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
    assert (Hx' : hs_partial h1 <= x < hs_partial h1 + APARTIAL) by lia.
    apply KEEP.
    + exact (df_blk_rng_x ly1 S1 Hp1 W m md _ _ x HAR Apb Hx').
    + intros Hg. apply (df_blk_gs_x ly1 S1 Hp1 W m md _ _ x HAR Apb Hx'). unfold ASRC in *. lia.
  - exact HW0.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity. }
apply (df_tail_xR cx Hp kr s1 D k p0 W regs' m' md' Q HR'); [| lia | exact Hnext | exact Hend].
exists ly1, S1, Hp1, k1, e1, h2.
apply (df_close_local_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 m' md' h2 b HB HC0 HJ').
- intros x Hx H1 _. exact (KEEP x Hx H1).
- intros x Hx. destruct ((df_cells_out B RG HGO HRGD) x Hx) as (Hr & Hng & _). apply KEEP; [exact Hr|].
  intros Hg. apply Hng. unfold ASRC in *. lia.
- exact PR.
- exact Hsrc2.
- exact Hb.
- exact Hst.
- exact Hnone.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

Lemma df_finish_add_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b regs' m' md' Q,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> (df_regs RG) cx s1 p0 k regs' -> Z.of_nat k < dnum s1 ->
df_cutjh_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
b <> 0 -> hs_overlong h1 = 0 -> hs_npartial h1 <> APARTIAL ->
AJGXR (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W m' md' k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) -> a <> hs_partial h1 + hs_npartial h1 ->
   abyte_kept W m W m' a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
val_mem SEGS (arm W m') (dHA RG cx + 48) 8 (hs_npartial h1 + 1) ->
val_mem SEGS (arm W m') (dHA RG cx + 56) 4 0 ->
val_mem SEGS (arm W m') (hs_partial h1 + hs_npartial h1) 1 b ->
(forall W2 c2, DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S k) W2 c2 -> SRrG SEGS R W2 c2 Q) ->
(forall W2 c2, DE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W2 c2 -> SRrG SEGS R W2 c2 Q) ->
SRrG SEGS R W (cfg_at SEGS (BASE + A_df_tail) regs' m' md') Q.
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b regs' m' md' Q HB HR' Hk HC Hb Hb0 Hov0 HnpA HJ' KEEP PR
  V48 V56 Vb Hnext Hend.
destruct (df_src_byte_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b HC Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & Hb8).
pose proof HC as HC0.
destruct HC as (tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 & _ & _ & _ & _ & _ & HMEM & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _).
assert (HAR : ARx ly1 S1 Hp1 W m md) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Anp & Aovl & Apb & Apj & Apg & AnoW & _).
assert (HAe : dHA RG cx = rg_s RG + ASRC * Z.of_nat (dxj cx)) by reflexivity.
pose proof HGSB as (HGlo & HGhi & HGal).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
assert (HAlo : rg_s RG <= dHA RG cx) by (rewrite HAe; unfold ASRC; lia).
assert (HAhi : dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (rewrite HAe; unfold ASRC in *; lia).
set (np := hs_npartial h1) in *.
assert (Hnp : 0 <= np < APARTIAL) by (unfold APARTIAL in *; lia).
set (i := Z.to_nat np).
assert (Hi : (i < length (hs_pjunk h1))%nat) by (unfold i, APARTIAL in *; lia).
assert (Hiz : Z.of_nat i = np) by (unfold i; lia).
set (pj2 := df_updb (hs_pjunk h1) i (Z_to_bv 8 b)).
set (h2 := HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
  pj2 (np + 1) 0 (hs_pad h1) (hs_expected h1) (hs_held h1)).
assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) ->
  ~ (hs_partial h1 <= a < hs_partial h1 + APARTIAL) -> abyte_kept W m W m' a).
{ intros x Hx H1 H2. apply KEEP; [exact Hx | exact H1 |]. intros ->. apply H2. lia. }
assert (Hpw : hs_W h2 = firstn i (hs_pjunk h1) ++ [Z_to_bv 8 b]).
{ unfold hs_W. cbn [hs_pjunk hs_npartial h2]. replace (Z.to_nat (np + 1)) with (S i) by (unfold i; lia).
  rewrite (df_firstn_nth_app pj2 i (Z_to_bv 8 b) ((df_updb_nth RG) _ _ _ Hi)). unfold pj2. rewrite df_updb_firstn.
  reflexivity. }
assert (Hsrc2 : asrc_at B ly1 S1 W m' (dHA RG cx) h2).
{ apply (df_asrc_upd_x ly1 S1 Hp1 W m md m' (dHA RG cx) h1 h2 HAR Hsrc HAlo HAhi KX PR V48 V56).
  - cbn [hs_npartial h2]. unfold APARTIAL in *. lia.
  - left. reflexivity.
  - cbn [hs_pjunk h2]. unfold pj2. rewrite df_updb_len. exact Apj.
  - cbn [hs_pjunk h2]. unfold pj2. rewrite df_updb_bzs.
    assert (Hbz : bz (Z_to_bv 8 b) = b) by exact (df_bz_of b Hb8).
    rewrite Hbz.
    apply (garr8_upd SEGS (arm W m) (arm W m') (hs_partial h1) (bzs (hs_pjunk h1)) i b Apg).
    + unfold bzs. rewrite length_map. exact Hi.
    + rewrite Hiz. exact Vb.
    + exact Hb8.
    + intros x Hx Hne. unfold arm. apply (mbyte_of_aview SEGS).
      unfold bzs in Hx. rewrite length_map, Apj in Hx.
      assert (Hx' : hs_partial h1 <= x < hs_partial h1 + APARTIAL) by lia.
      apply (proj1 (KEEP x (df_blk_rng_x ly1 S1 Hp1 W m md _ _ x HAR Apb Hx') ltac:(intros Hg;
        apply (df_blk_gs_x ly1 S1 Hp1 W m md _ _ x HAR Apb Hx'); unfold ASRC in *; lia) ltac:(rewrite <- Hiz; exact Hne))).
  - rewrite Hpw. intros Hin. apply in_app_or in Hin as [Hin | [Hin | []]].
    + apply AnoW. unfold hs_W. exact Hin.
    + apply Hb0. apply (f_equal bz) in Hin. rewrite (df_bz_of b Hb8), (df_bz_of 0 ltac:(lia)) in Hin. exact Hin.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity. }
apply (df_tail_xR cx Hp kr s1 D k p0 W regs' m' md' Q HR'); [| lia | exact Hnext | exact Hend].
exists ly1, S1, Hp1, k1, e1, h2.
apply (df_close_local_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 m' md' h2 b HB HC0 HJ').
- exact KX.
- intros x Hx. destruct ((df_cells_out B RG HGO HRGD) x Hx) as (Hr & Hng & Himg). apply KEEP; [exact Hr | |].
  + intros Hg. apply Hng. unfold ASRC in *. lia.
  + intros ->. pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & HrqA).
    apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W m md (hs_partial h1) APARTIAL (hs_partial h1 + np) HAR Apb);
      [|exact Himg].
    clear - Hnp HrqA. lia.
- exact PR.
- exact Hsrc2.
- exact Hb.
- rewrite ((df_step_add RG HGSB) h1 b Hb0 Hov0 HnpA Anp Apj). cbn [fst].
  apply ((df_state_add RG HGSB) h1 h2 b); cbn [hs_overlong hs_npartial hs_pjunk h2].
  + reflexivity.
  + reflexivity.
  + lia.
  + unfold pj2. apply df_updb_firstn.
  + unfold pj2. apply (df_updb_nth RG). exact Hi.
  + exact Hb8.
- rewrite ((df_step_add RG HGSB) h1 b Hb0 Hov0 HnpA Anp Apj). reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

Lemma df_cutjh_src_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1,
df_cutjh_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> asrc_at B ly1 S1 W m (dHA RG cx) h1.
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 HC.
destruct HC as (tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 & _ & _ & _ & _ & _ & HMEM & _).
exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMEM))))))))).
Qed.

Lemma df_push_pre_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> df_cutjt_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl ->
nth_error (ddata s1) k = Some 0 -> hs_overlong h1 = 0 ->
alist_at B ly1 S1 W m (dHA RG cx + 64) (hs_expected h1) true /\
In (hs_partial h1, APARTIAL) (ablocks B ly1 S1) /\ hs_partial h1 <> hl_v (hs_expected h1) /\
garr8 SEGS (mrestrict (w_H W) m) (hs_partial h1) (bzs (hs_W h1)) /\
~ In (Z_to_bv 8 0) (hs_W h1) /\ Z.of_nat (length (hs_W h1)) <= APARTIAL /\
(lp_grow (hs_expected h1) = true -> lp_vbytes (hs_expected h1) < MMAX) /\
blocks_bytes S1 + tr_peak (lp_tr (hs_expected h1) (Z.of_nat (length (hs_W h1)))) <= LIVE_MAX /\
mo_ok MT S1 (lp_cost MT (hs_expected h1) (Z.of_nat (length (hs_W h1)))) /\
(forall a, inFP (lp_FP (hs_expected h1)) a ->
  (inFP (dFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a) /\
rp_RM RP S1 (Z.to_nat (lp_cost MT_rk (hs_expected h1) (Z.of_nat (length (hs_W h1)))) +
  df_kr2 (hs_expected h1) (Z.of_nat (length (hs_W h1))) tl kr) /\
cnt_ok_pk RP (lp_peak (hs_expected h1) (Z.of_nat (length (hs_W h1)))) (ablocks B ly1 S1).
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl HB HC Hnth Hov.
destruct HC as (out1 & ev1 & LB1 & spent & jb & ad & v0 & rs & r0 & rs0 &
  _ & _ & _ & _ & _ & HMEM & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hstate & Hen & Hecap & _ & HRS & HPFUT & HBUD).
destruct HBUD as (HBUD & HRM & HCNT).
destruct HMEM as (HJ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _ & _ & Hout & _ & Hperm).
destruct Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H16 & _ &
  H18 & _ & H20 & H21 & H22 & _ & H24).
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPerm0 & _ & _ & _ & _ & _ & HMok
  & _).
assert (HAR1 : ARx ly1 S1 Hp1 W m md) by (eapply ajournal_gx_AR_xR; exact HJ).
clear HJ.
pose proof H22 as (_ & _ & _ & _ & Hncap & Hvdisj & _).
assert (HC0 : 0 <= hl_cap (hs_expected h1)) by (clear - Hncap; unfold hl_n in Hncap; lia).
(* ---- the three capacities of the round state are >= 0 ---- *)
assert (HCP : 0 <= drain_b_c.ds_cap s1) by (destruct HRS as (_ & _ & Rg & _); clear - Rg; unfold ulen in Rg; lia).
assert (HOC : 0 <= drain_b_c.ds_ocap s1).
{ destruct Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & Hoc).
  clear - Hoc. destruct Hoc as [(E & _) | (P & _)]; lia. }
assert (HEC : 0 <= drain_b_c.ds_ecap s1).
{ destruct (Z_lt_le_dec (drain_b_c.ds_ecap s1) 0) as [Hlt|Hge]; [|exact Hge].
  pose proof ((df_pcapm_neg RG HGSB) (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1))) (drain_b_c.ds_en s1) _ Hlt) as X.
  rewrite <- Hecap in X. clear - X HC0. lia. }
clear Hout HRS.
(* ---- the requests: this push first, then the rest of the round's pushes, then the later requests ---- *)
pose proof (df_step_push h1 Hov) as STP.
unfold dpfut in HPFUT. cbv zeta in HPFUT.
rewrite (df_pu_skipn_cons (ddata s1) k 0 Hnth), lines_cons, <- Hstate, STP in HPFUT.
cbn [drain_b_c.pushes_run fst snd] in HPFUT.
destruct HPFUT as (tl2 & HDR & Htl).
pose proof ((df_tnn_drfut RG HGSB) cx s1 _ _ tl2 HCP HEC HOC HDR) as TN3.
clear HDR.
rewrite <- Hen, <- Hecap in Htl.
assert (ELW : length (bzs (hs_W h1)) = length (hs_W h1)) by (unfold bzs; apply length_map).
rewrite ELW in Htl.
lazymatch type of Htl with
| _ = (_ ++ fst (fst (drain_b_c.pushes_run ?n1 ?c1 ?ls1 ?j1 ?v1 ?rs1))) ++ _ =>
  pose proof (proj1 ((df_tnn_pushes RG HGSB) ls1 n1 c1 j1 v1 rs1
    ((df_push_cap_nn RG HGSB) (hl_n (hs_expected h1)) (hl_cap (hs_expected h1)) HC0))) as TN2
end.
pose proof ((df_tnn_cost MT RG MTL HGSB) _ TN2) as C2. pose proof ((df_tnn_cost MT RG MTL HGSB) _ TN3) as C3.
pose proof (mo_free_nonneg MT MTL) as F0.
pose proof ((df_lpcost_nn MT RG MTL HGSB) (hs_expected h1) (Z.of_nat (length (hs_W h1))) HC0 (Nat2Z.is_nonneg _)) as LC0.
lazymatch type of Htl with
| _ = (?T1 ++ ?T2) ++ _ =>
  rewrite Htl in HBUD;
  destruct HBUD as (Bl & _ & Bc & Ba & Bm);
  rewrite ((df_pu_tr_cost_app MT RG) (T1 ++ T2) tl2), ((df_pu_tr_cost_app MT RG) T1 T2) in Bc;
  rewrite <- app_assoc in Ba;
  rewrite ((df_pu_tr_max_app RG HGSB) (T1 ++ T2) tl2), ((df_pu_tr_max_app RG HGSB) T1 T2) in Bm
end.
rewrite <- ((df_pu_lp_cost MT RG) (hs_expected h1) v0 (Z.of_nat (length (hs_W h1)))) in Bc.
match type of Ba with _ + tr_peak (?T1 ++ ?R) <= _ => pose proof (W_tr_peak.tr_peak_prefix T1 R) as Ba1 end.
(* the count premise: list_push's peak is at most 2, within the requests' own peak plus 2 *)
assert (HCNT2 : cnt_ok_pk RP (lp_peak (hs_expected h1) (Z.of_nat (length (hs_W h1)))) (ablocks B ly1 S1)).
{ eapply cnt_ok_pk_mono; [|exact HCNT].
  intros P. unfold lp_peak. cbv beta.
  destruct (P (lp_vbytes (hs_expected h1)) && lp_grow (hs_expected h1)), (P (Z.of_nat (length (hs_W h1)) + 1)); lia. }
(* the room premise: list_push's charge and the room of the requests after it (df_kr2) *)
assert (HRM2 : rp_RM RP S1 (Z.to_nat (lp_cost MT_rk (hs_expected h1) (Z.of_nat (length (hs_W h1)))) +
  df_kr2 (hs_expected h1) (Z.of_nat (length (hs_W h1))) tl kr)).
{ rewrite Htl, <- app_assoc in HRM |- *.
  exact (df_pu_room_pre _ _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl HRM). }
clear Htl HRM HCNT.
refine (conj H22 (conj H18 (conj _ (conj _ (conj H21 (conj _ (conj _ (conj _ (conj _ (conj _
  (conj HRM2 HCNT2))))))))))).
- (* h->partial is not the expected list's vector *)
  intros Heq. destruct Hvdisj as [(Hc0 & Hv0) | (Hcp & _)].
  + destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W m md _ _ HAR1 H18) as (_ & H4096 & _).
    clear - H4096 Heq Hv0. lia.
  + apply NoDup_ListNoDup in H24. unfold hs_blocks in H24. cbn [app] in H24.
    apply List.NoDup_remove_2 in H24. apply H24. apply in_or_app. right. apply in_or_app. left.
    rewrite Heq. unfold list_blocks.
    rewrite (proj2 (Z.eqb_neq (hl_cap (hs_expected h1)) 0) ltac:(clear - Hcp; lia)).
    left. reflexivity.
- (* the partial line's bytes: the first npartial of the buffer *)
  unfold hs_W. rewrite <- (firstn_skipn (Z.to_nat (hs_npartial h1)) (hs_pjunk h1)) in H20.
  unfold bzs in H20 |- *. rewrite map_app in H20. exact (proj1 (proj1 (garr8_app _ _ _ _ _) H20)).
- assert (LW : (length (hs_W h1) <= Z.to_nat (hs_npartial h1))%nat)
    by (unfold hs_W; rewrite length_firstn; apply Nat.le_min_l).
  clear - LW H16. unfold APARTIAL in *. lia.
- intros G. pose proof ((df_pp_max RG HGSB) v0 (hs_expected h1) (Z.of_nat (length (hs_W h1))) G) as X.
  clear - X Bm. lia.
- (* C3: list_push's requests open the trace still owed, so their peak is within that trace's (W_tr_peak.v
     tr_peak_prefix; the requests' sizes do not depend on the names, list_push_tra_sz) *)
  unfold lp_tr.
  destruct (W_tr_peak.tr_sz_measures _ _ (W_tr_peak.list_push_tra_sz v0 RelayRunF.adr0 (hl_n (hs_expected h1))
    (hl_cap (hs_expected h1)) (Z.of_nat (length (hs_W h1))))) as (E & _).
  rewrite <- E. clear - Ba Ba1. lia.
- apply (mok_station MT (dxS cx) S1 _ spent _ MTL HMok Bl); [exact LC0|].
  clear - Bc C2 C3 F0. lia.
- (* the footprint: an entry block of drain's own footprint, or a block the walk allocated *)
  unfold lp_FP. destruct (Z.eqb_spec (hl_cap (hs_expected h1)) 0) as [Ec|Ec];
    intros a Ha; [exfalso; exact (inFP_nil a Ha)|].
  destruct Ha as (r & Hr & Hra). cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Hra.
  destruct Hvdisj as [(Hc0 & _) | (_ & Hinv & _)]; [exfalso; exact (Ec Hc0)|].
  pose proof (req_size_pos (AREC * hl_cap (hs_expected h1)) ltac:(clear - HC0; unfold AREC; lia)) as (_ & Hrq).
  assert (HinS : In (hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1)) (asrc_blks h1)).
  { unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. unfold alist_blks.
    rewrite (proj2 (Z.eqb_neq (hl_cap (hs_expected h1)) 0) Ec). apply in_or_app. left. left. reflexivity. }
  destruct (in_dec df_pair_dec (hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))
    (ablocks B (dxly cx) (dxS cx))) as [Hin0|Hnin0].
  + left. split;
      [|exists (hl_v (hs_expected h1)), (AREC * hl_cap (hs_expected h1)); split; [exact Hinv | clear - Hra Hrq; lia]].
    pose proof (df_pu_ne_in_x ly1 S1 Hp1 W m md (dxG cx, ATABLE) _ _ HAR1 Hperm
      (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl HinS))))) as HNE.
    cbn [fst] in HNE.
    assert (ND : List.NoDup (map fst (asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx))).
    { apply (df_pu_nd_x ly1 S1 Hp1 W m md _ ((dxG cx, ATABLE) :: aentry_blks e1) [] HAR1).
      rewrite app_nil_r. exact Hperm. }
    pose proof (df_nd_fst _ _ _ ND HinS) as NR.
    pose proof (Permutation_in _ HPerm0 Hin0) as Hin1.
    assert (HinF : In (hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))
      (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx))).
    { destruct Hin1 as [Eq|Hin1]; [injection Eq as E1 E2; exfalso; exact (HNE E1)|].
      apply in_app_or in Hin1 as [Q|Hin1]; [apply in_or_app; left; exact Q|].
      apply in_app_or in Hin1 as [Q|Hin1]; [apply in_or_app; right; apply in_or_app; left; exact Q|].
      apply in_app_or in Hin1 as [Q|Q]; [apply in_or_app; right; apply in_or_app; right; exact Q|].
      exfalso. apply NR. apply in_or_app. right. exact Q. }
    exists (hl_v (hs_expected h1), hl_v (hs_expected h1) + req_size (AREC * hl_cap (hs_expected h1))).
    split; [|cbn [fst snd]; clear - Hra Hrq; lia].
    unfold dFP, dr_fp. right. unfold ablocks_fp.
    exact (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ _ HinF).
  + right. exists (hl_v (hs_expected h1)), (AREC * hl_cap (hs_expected h1)).
    split; [exact Hinv|]. split; [exact Hnin0|]. clear - Hra Hrq; lia.
Qed.

Lemma df_keep_hi_xR : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
(forall a, inG G1 a -> inG (G_DR B RG) a) ->
AJGXR G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Hsub HJ a Ha Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
rewrite (F1 a Ha Hno). apply (aview_gagree SEGS G1 (w_H W) memc memS a Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by (clear - Ha C1; lia).
intros Hc. pose proof (pa_segs_low a (proj1 (HG a (Hsub a Hc)))) as Hlo.
clear - Hlo Ha C1 C5. lia.
Qed.

Lemma df_keep_img_xR : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
~ YI16.sink_open_fp FP1 ->
AJGXR G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> ~ inG G1 a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Hfp HJ a Hi Ho He Hpst Hna.
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof (pa_segs_low a Hi) as Hlo.
rewrite (F3 a Hi Ho He Hpst ltac:(intros Hso; exfalso; exact (Hfp Hso))).
apply (aview_gagree SEGS G1 (w_H W) memc memS a Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by (unfold kLowMemEnd in Hlo; clear - Hlo; lia).
exact Hna.
Qed.

Lemma df_keep_blk_xR : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 p n,
(forall a, inG G1 a -> inG (G_DR B RG) a) ->
ARx lyc Sc Hpc W memc mdc ->
AJGXR G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
In (p, n) (ablocks B lyc Sc) -> (forall i, 0 <= i < req_size n -> ~ inFP FP1 (p + i)) ->
In (p, n) (ablocks B ly2 S2) /\
(forall i, 0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) memc (p + i)).
Proof.
intros G1 STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 p n Hsub HAR HJ Hin Hno.
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc p n HAR Hin) as (_ & H4096 & Hceil & _).
pose proof (req_size_pos n (BLKN lyc Sc Hpc W memc mdc p n HAR Hin)) as (Hrq & _).
pose proof HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _ & _ & Hgone & _).
assert (Hin2 : In (p, n) (ablocks B ly2 S2)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B ly2 S2)) as [Hc|Hc];
  [exact Hc | exfalso; exact (Hno 0 ltac:(clear - Hrq; lia) (Hgone p n 0 Hin Hc ltac:(clear - Hrq; lia)))]. }
split; [exact Hin2|]. intros i Hi.
rewrite (F2 p n i Hin Hin2 Hi (Hno i Hi)).
apply (aview_gagree SEGS G1 (w_H W) memc memS (p + i) Hag).
apply (proj2 (inGb_false G1 _)). rewrite unsigned_lit_small by (clear - H4096 Hceil Hi ACL; lia).
intros Hc.
destruct (alx_client_img _ _ _ LAWS lyc Sc Hpc W memc mdc (p + i) HAR
  ltac:(left; exists p, n; split; [exact Hin | clear - Hi; lia])) as [_ Hni].
exact (Hni (proj1 (HG (p + i) (Hsub (p + i) Hc)))).
Qed.

Lemma df_gx_pres_xR : forall G0 STK sp0 FP ly S Hp (W0 : world SEGS) mem md own ly' S' Hp' (W' : world SEGS) mem' md' k,
AJGXR G0 0 [] STK sp0 FP ly S Hp W0 mem md own ly' S' Hp' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros G0 STK sp0 FP ly S Hp W0 mem md own ly' S' Hp' W' mem' md' k HJ a Ha.
destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _). exact (Hpr a Ha).
Qed.

Lemma df_lp_call_xR : forall cx Hp kr ly1 S1 Hp1 k1 W mc mdc regsc raw (l : hlist) (x : list byte) q qn kr2 Q,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
AJGXR (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W mc mdc k1 ->
spZ regsc = dsp0 cx - DRAIN_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> s0Z regsc < alloc_ceiling ->
getr regsc 10 = w64 (dHA RG cx + 64) -> getr regsc 11 = w64 q -> getr regsc 12 = w64 (Z.of_nat (length x)) ->
alist_at B ly1 S1 W mc (dHA RG cx + 64) l true ->
In (q, qn) (ablocks B ly1 S1) -> q <> hl_v l -> q + Z.of_nat (length x) <= q + req_size qn ->
garr8 SEGS (mrestrict (w_H W) mc) q (bzs x) ->
~ In (Z_to_bv 8 0) x -> Z.of_nat (length x) <= APARTIAL ->
(lp_grow l = true -> lp_vbytes l < MMAX) ->
blocks_bytes S1 + tr_peak (lp_tr l (Z.of_nat (length x))) <= LIVE_MAX ->
mo_ok MT S1 (lp_cost MT l (Z.of_nat (length x))) ->
(forall a, inFP (lp_FP l) a ->
  (inFP (dFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a) ->
rp_RM RP S1 (Z.to_nat (lp_cost MT_rk l (Z.of_nat (length x))) + kr2) ->
cnt_ok_pk RP (lp_peak l (Z.of_nat (length x))) (ablocks B ly1 S1) ->
(forall W2 ly2 S2 Hp2 kk regs2 m2 md2 (l2 : hlist) d,
  AJGXR (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
    (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 kk ->
  aregs_preserved regsc regs2 ->
  (forall p n i, In (p, n) (ablocks B ly1 S1) -> p <> hl_v l -> 0 <= i < req_size n ->
     abyte_kept W mc W2 m2 (p + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> ~ (dHA RG cx + 64 <= a < dHA RG cx + 80) -> abyte_kept W mc W2 m2 a) ->
  (forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mc W2 m2 a) ->
  (forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W mc W2 m2 a) ->
  rom_view SEGS W2 m2 -> apres_kept B W mc W2 m2 -> frames S2 = frames S1 ->
  alist_at B ly2 S2 W2 m2 (dHA RG cx + 64) l2 true ->
  hl_recs l2 = hl_recs l ++ [(d, x)] ->
  hl_cap l2 = ListRep.grow_cap (hl_n l) (hl_cap l) ->
  (lp_grow l = false -> hl_v l2 = hl_v l) ->
  (forall rest,
   Permutation (ablocks B ly1 S1)
     ((if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []) ++ rest) ->
   Permutation (ablocks B ly2 S2)
     ((d, Z.of_nat (length x) + 1) :: (if lp_grow l then [(hl_v l2, AREC * hl_cap l2)] else []) ++ rest)) ->
  mo_le MT S1 S2 (lp_cost MT l (Z.of_nat (length x))) ->
  rp_RM RP S2 kr2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 raw m2 (seg_rom SEGS)) md2) Q) ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_list_push)) mc (seg_rom SEGS)) mdc) Q.
Proof.
intros cx Hp kr ly1 S1 Hp1 k1 W mc mdc regsc raw l x q qn kr2 Q HB HJ Hsp Hgp Htp Hra Hraw Hra4 Hs0 H10 H11 H12 HL
  Hq Hqv Hqr Hsrc Hnz Hlen Hgrow Hbb Hmo HFP HRM HCNT HK.
pose proof HB as ((_ & _ & _ & _ & _ & Hstk0 & _) & _ & _ & _ & _ & _ & _ & _ & Hj & _ & _ & _ & _ & _ & _ & Hrv0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HspR : alloc_ceiling + DRAIN_STK_x <= dsp0 cx <= 2 ^ 47) by (unfold dsp0; clear - Hceil Hslo Hshi H47; lia).
clear Hstk0 Hceil Hslo Hshi H47.
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; clear - Hj; lia).
(* the callee's G: h->expected, 16 bytes of g_s[j] *)
assert (Hsub : forall a, inG [(dHA RG cx + 64, 16)] a -> inG (G_DR B RG) a).
{ intros a Ha. apply (proj1 (df_G1_in _ a)) in Ha.
  exact (proj1 ((df_pu_gs B RG HRGD) a ltac:(clear - Ha HAr; unfold ASRC in *; lia))). }
assert (HG1 : gx_ok SEGS B [(dHA RG cx + 64, 16)]) by exact (gx_ok_sub SEGS B _ _ Hsub HG).
assert (HR1 : gx_rt B [(dHA RG cx + 64, 16)]).
{ intros a Ha. apply (proj1 (df_G1_in _ a)) in Ha.
  pose proof ((df_pu_zpw RG) _ 0%nat 2%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D0.
  pose proof ((df_pu_zpw RG) _ 1%nat 2%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D1.
  pose proof ((df_pu_zpw RG) _ 2%nat 11%nat (0, 0) HRGD ltac:(clear; lia) ltac:(clear; cbn [length]; lia)) as D2.
  cbn [nth] in D0, D1, D2. unfold zdisj in D0, D1, D2. cbn [fst snd] in D0, D1, D2.
  clear - D0 D1 D2 Ha HAr. unfold ASRC in *. repeat split; lia. }
assert (HZ1 : azs B (dHA RG cx + 64) 16).
{ apply ((df_azs_sub B RG HGSB) (rg_s RG) (4 * ASRC));
  [exact HGSZ | clear - HAr; unfold ASRC in *; lia | clear - HAr; unfold ASRC in *; lia]. }
assert (Hx16 : Z.of_nat (length x) < 2 ^ 16) by (unfold APARTIAL in Hlen; clear - Hlen; lia).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
pose proof (df_lpfp_pos_x ly1 S1 Hp1 W mc mdc (dHA RG cx + 64) l true HARc HL) as HFPc.
assert (C16 : (- DRAIN_FRAME) mod 16 = 0) by reflexivity.
assert (Cneg : - DRAIN_FRAME <= 0) by (apply Z.leb_le; reflexivity).
assert (CLP : 0 <= LP_STK) by (apply Z.leb_le; reflexivity).
assert (CBUD : LP_STK - - DRAIN_FRAME <= DRAIN_STK_x) by (apply Z.leb_le; reflexivity).
(* the call: LPSPECR at G1, composed into drain's journal *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (df_gx_call_xR R_trans [(dHA RG cx + 64, 16)] W regsc mc (BASE + AF_fr_list_push) DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) ly1 S1 Hp1 mdc k1 LP_STK (lp_FP l) (- DRAIN_FRAME) raw []
    (fun ly2 S2 Hp2 W2 regs2 mem2 md2 kk => exists (l2 : hlist) (d : Z),
       alist_at B ly2 S2 W2 mem2 (dHA RG cx + 64) l2 true /\
       hl_recs l2 = hl_recs l ++ [(d, x)] /\ hl_cap l2 = ListRep.grow_cap (hl_n l) (hl_cap l) /\
       (lp_grow l = false -> hl_v l2 = hl_v l) /\
       (forall rest,
        Permutation (ablocks B ly1 S1)
          ((if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []) ++ rest) ->
        Permutation (ablocks B ly2 S2)
          ((d, Z.of_nat (length x) + 1) :: (if lp_grow l then [(hl_v l2, AREC * hl_cap l2)] else []) ++ rest)) /\
       apres_kept B W mc W2 mem2 /\
       (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) mc (as_errno B + i)) /\
       frames S2 = frames S1 /\ mo_le MT S1 S2 (lp_cost MT l (Z.of_nat (length x))) /\ rp_RM RP S2 kr2)
    Hsub HJ Hsp C16 Cneg CLP CBUD Hgp Htp Hra Hraw Hra4 (achain_low _ _ _ _ Hs0)).
  - intros HPRE1. eapply (SRrG_mono SEGS R).
    { assert (HLA8 : (dHA RG cx + 64) mod 8 = 0).
      { unfold dHA, ASRC. destruct HGSB as (_ & _ & HG8). clear - HG8.
        apply Z.mod_divide in HG8; [|lia]. destruct HG8 as [k8 Hk8].
        apply Z.mod_divide; [lia|]. exists (k8 + 12 * Z.of_nat (dxj cx) + 8). lia. }
      exact (LPSPECR [(dHA RG cx + 64, 16)] HG1 HR1 W ly1 S1 Hp1 regsc mc mdc [] (dHA RG cx + 64) q l true x q qn HPRE1
        H10 H11 H12 HLA8 HL (fun a Ha => proj2 (df_G1_in _ a) Ha) HZ1 Hgrow Hx16 Hbb Hq Hqv (Z.le_refl q) Hqr Hsrc
        (fun _ => conj Hnz Hlen) ltac:(intros E; discriminate E) Hmo kr2 HRM HCNT). }
    cbv beta. unfold lp_post_xR.
    intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & l2 & d & -> & HJ2 & HP2 & HAL & Hrecs & Hcap & Hgv &
      HPerm & HPK & Herr & HFr & HMLE & HRM2).
    exists ly2, S2, Hp2, regs2, mem2, md2, kk.
    split; [rewrite Hra; reflexivity|]. split; [rewrite Hsp in HJ2; exact HJ2|]. split; [exact HP2|].
    exists l2, d. split; [exact HAL|]. split; [exact Hrecs|]. split; [exact Hcap|]. split; [exact Hgv|].
    split; [exact HPerm|]. split; [exact HPK|]. split; [exact Herr|]. split; [exact HFr|].
    split; [exact HMLE | exact HRM2].
  - exact HFP. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJa & HJb & HP &
  (l2 & d & HAL & Hrecs & Hcap & Hgv & HPerm & HPK & Herr & HFr & HMLE & HRM2)).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJb) as HAR2.
apply (HK W2 ly2 S2 Hp2 (k1 + kk) regs2 mem2 md2 l2 d).
- exact HJa.
- exact HP.
- (* a live block other than the vector: outside lp_FP l, so the callee's block clause keeps it, and alive *)
  intros p n i Hin Hne Hi.
  destruct (df_keep_blk_xR [(dHA RG cx + 64, 16)] LP_STK (dsp0 cx + - DRAIN_FRAME) (lp_FP l) ly1 S1 Hp1 W mc mdc
    ly2 S2 Hp2 W2 mem2 md2 kk p n Hsub HARc HJb Hin
    (df_lpfp_out_x ly1 S1 Hp1 W mc mdc (dHA RG cx + 64) l true p n HARc HL Hin Hne)) as [Hin2 Hv].
  split; [exact (Hv i Hi) | intros _; exact (df_blk_wr_x ly2 S2 Hp2 W2 mem2 md2 p n HAR2 Hin2 i Hi)].
- (* an image byte off h->expected and off PST: the callee's image clause, its presence by apres_kept *)
  intros a Hi Ho He Hpst Hn. split.
  + apply (df_keep_img_xR [(dHA RG cx + 64, 16)] LP_STK (dsp0 cx + - DRAIN_FRAME) (lp_FP l) ly1 S1 Hp1 W mc mdc
      ly2 S2 Hp2 W2 mem2 md2 kk HFPc HJb a Hi Ho He Hpst).
    intros Hc. apply Hn. apply (proj1 (df_G1_in _ a)) in Hc. clear - Hc. lia.
  + exact (df_wr_img W W2 mc mem2 a Hi (HPK a Hi Ho He)).
- (* errno: lp_post's view, and a writable segment's byte *)
  intros a Ha.
  assert (Hv : aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mc a).
  { replace a with (as_errno B + (a - as_errno B)) by ring. apply Herr. clear - Ha. lia. }
  assert (HeG : inG (G_DR B RG) a).
  { unfold G_DR, G_SL, inG. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    clear - Ha. lia. }
  split; [exact Hv|]. intros Hw.
  apply (df_err_wr W W2 mc mem2 a (proj1 (HG a HeG))); [|exact Hv|exact Hw].
  intros Hr. exact (proj1 (proj2 (proj2 (HROMO a Hr))) Ha).
- (* drain's frame: above the callee's window, kept by its stack clause; present by drain's journal *)
  intros a Ha. split.
  + apply (df_keep_hi_xR [(dHA RG cx + 64, 16)] LP_STK (dsp0 cx + - DRAIN_FRAME) (lp_FP l) ly1 S1 Hp1 W mc mdc
      ly2 S2 Hp2 W2 mem2 md2 kk Hsub HJb a).
    * clear - HspR Ha. unfold DRAIN_STK_x, DRAIN_STK, SL_STK, SL_FRAME, ASTACK, DRAIN_FRAME in *. lia.
    * clear - Ha. lia.
  + intros _. apply (apresent_writable SEGS).
    apply (df_gx_pres_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJa).
    clear - Ha. unfold DRAIN_STK_x, DRAIN_STK, SL_STK, SL_FRAME, ASTACK, DRAIN_FRAME in *. lia.
- eapply ajournal_gx_rom_view_xR; first [exact HJa | exact HROMO | exact PSTR | exact Hrv0 | exact LAWS
    | exact pa_segs_low].
- exact HPK.
- exact HFr.
- exact HAL.
- exact Hrecs.
- exact Hcap.
- exact Hgv.
- exact HPerm.
- exact HMLE.
- exact HRM2.
Qed.

Lemma df_cutjh_sp_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 regs,
(df_regs RG) cx s1 p0 k regs -> df_cutjh_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 ->
alloc_ceiling <= spZ regs <= 2 ^ 47.
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 regs HR HC.
pose proof HR as (R2 & _).
destruct HC as (tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 & _ & _ & _ & _ & _ & HMEM & _).
pose proof HMEM as (HJ & _).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
rewrite R2. lia.
Qed.

Lemma df_body_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W regs m md e1 h1 b Q,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> (df_regs RG) cx s1 p0 k regs -> Z.of_nat k < dnum s1 ->
df_cutjh_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
(forall W2 c2, DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S k) W2 c2 -> SRrG SEGS R W2 c2 Q) ->
(forall W2 c2, DE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W2 c2 -> SRrG SEGS R W2 c2 Q) ->
SRrG SEGS R W (cfg_at SEGS (BASE + A_dr_feed) regs m md) Q.
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W regs m md e1 h1 b Q HB HR Hk HC Hb Hnext Hend.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof HGSB as (HGlo & HGhi & HGal).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hj & _).
pose proof HR as (R2 & R3 & R4 & R18 & R9 & R8 & R21 & R23 & R19 & R25 & R26 & R24 & R20 & R27 & R22).
destruct (df_src_byte_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b HC Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & Hb8).
pose proof (df_cutjh_src_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 HC) as Hsrc.
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Anp & Aovl & Apb & Apj & Apg & AnoW & _).
assert (Rb : 0 <= b < 2 ^ 64) by lia.
assert (Rov : 0 <= hs_overlong h1 < 2 ^ 64) by (destruct Aovl as [-> | ->]; lia).
assert (Rnp : 0 <= hs_npartial h1 < 2 ^ 64) by (unfold APARTIAL in Anp; lia).
destruct (df_entry_full_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W regs m md e1 h1 b HB HR Hk HC Hb) as (HS & SHOK).
pose proof (df_cutjh_journal_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 HC) as HJ.
remember (Eimg (Ereg regs (df_extra (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn'. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn'. }
assert (E33 : ew E 33 = Z_to_bv 64 (hs_npartial h1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hs_overlong h1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 b)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E32 : ew E 32 = Z_to_bv 64 (hs_partial h1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E36 : ew E 36 = Z_to_bv 64 (hs_partial h1 + hs_npartial h1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (HAe : dHA RG cx = rg_s RG + ASRC * Z.of_nat (dxj cx)) by reflexivity.
assert (U23 : bv_unsigned (ew E 23) = dHA RG cx).
{ rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64. apply unsigned_lit_small. rewrite HAe. unfold ASRC in *. lia. }
assert (E23 : ew E 23 = Z_to_bv 64 (dHA RG cx)) by (rewrite (EE 23%nat 23%bv eq_refl), R23; reflexivity).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl), R21; reflexivity).
assert (HAr : 0x10000 <= dHA RG cx /\ dHA RG cx + 96 <= 0x5fb000)
  by (rewrite HAe; unfold ASRC in *; clear - HGlo HGhi Hj; lia).
clear HE.
assert (MEQ : forall x : word, ~ df_Pg (dHA RG cx) (bv_unsigned x) -> mrestrict (w_H W) m x = mrestrict (w_H W) m x)
  by (intros; reflexivity).
assert (PR : forall a, apresent (w_H W) m a -> apresent (w_H W) m a) by (intros a Ha; exact Ha).
unfold cfg_at.
paj_run_tok_xR RUNR HS HJ SHOK DFspan. { df_awr U23 HAe. }
df_track m MEQ PR U23.
psrr_branch_tok RUNR BRR HS SHOK DFspan.
- (* 0x8349c taken: b = 0 *)
  rewrite branch_eq_U, df_U0 in Hc. df_Uat Hc 35%nat b E35 Rb. apply Z.eqb_eq in Hc. rename Hc into Hb0.
  paj_run_tok_xR RUNR HS HJ SHOK DFspan. { df_awr U23 HAe. }
  df_track m MEQ PR U23.
  psrr_branch_tok RUNR BRR HS SHOK DFspan.
  + (* 0x834d0 taken: overlong <> 0, reset *)
    rewrite branch_ne_U, df_U0 in Hc. df_Uat Hc 34%nat (hs_overlong h1) E34 Rov.
    pose proof (df_ovl_nz _ Aovl Hc) as Hov1. clear Hc.
    df_leaf_runR HS HJ SHOK U23 HAe m MEQ PR 1%nat.
    refine (df_finish_nw_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b _ _ _ 0 0 Q HB _ Hk HC Hb HJ
      ((df_keep_of_meq RG) W m _ (df_Pg (dHA RG cx)) MEQ PR) PR _ _ _ _ _ _ _ Hnext Hend).
    * df_regs_tac HS HR EE E23 E21 HAr R20 R27 R22.
    * df_v (dHA RG cx) U23 48 8%N (SLit 0) 0; [reflexivity | cbn; lia].
    * df_v (dHA RG cx) U23 56 4%N (SLit 0) 0; [reflexivity | cbn; lia].
    * unfold APARTIAL. lia.
    * left. reflexivity.
    * rewrite Hb0, (df_step_reset h1 Hov1). apply df_state_reset; reflexivity.
    * rewrite Hb0, (df_step_reset h1 Hov1). reflexivity.
    * intros [].
  + (* 0x834d0 fall: overlong = 0, push *)
    rewrite branch_ne_U, df_U0 in Hc. df_Uat Hc 34%nat (hs_overlong h1) E34 Rov.
    pose proof (df_ovl_z _ Hc) as Hov0. clear Hc.
    (* ---- the call list_push (&h->expected, h->partial, h->npartial) at 0x834f0 ---- *)
    subst b.
    pose proof (df_cutjh_journal_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 HC) as HJ0.
    assert (HAR0 : ARx ly1 S1 Hp1 W m md) by (eapply ajournal_gx_AR_xR; exact HJ0).
    pose proof HC as (tl & HCt).
    destruct (df_push_pre_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl HB HCt Hb Hov0)
      as (PAL & PPB & PNE & PG8 & PNZ & PLEN & PGR & PLIVE & PMO & PFP & PRM & PCNT).
    pose proof (df_cutjh_sp_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 regs HR HC) as Hsp.
    pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & HrqA).
    pose proof HB as (HPRE0 & _).
    pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
    assert (HAlo : rg_s RG <= dHA RG cx) by (rewrite HAe; unfold ASRC; clear; lia).
    assert (HAhi : dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (rewrite HAe; unfold ASRC in *; clear - Hj; lia).
    paj_run_to_tok_xR RUNTOR HS HJ SHOK DFspan AF_fr_list_push. { df_awr U23 HAe. }
    df_track m MEQ PR U23.
    pmkst HS.
    df_reg HS (2%bv : bv 5) Q2. df_reg HS (3%bv : bv 5) Q3. df_reg HS (4%bv : bv 5) Q4. df_reg HS (8%bv : bv 5) Q8.
    df_reg HS (10%bv : bv 5) Q10. df_reg HS (11%bv : bv 5) Q11. df_reg HS (12%bv : bv 5) Q12.
    prreg HS (1%bv : bv 5) T1.
    lazymatch goal with |- SRrG _ _ _ {| cfg_ms := mkst (ms_regs ?ms0) _ (ms_mem ?ms0) _; cfg_model := ?md0 |} _ =>
      set (rc0 := ms_regs ms0) in *; set (mc := ms_mem ms0) in *; set (mdc := md0) in * end.
    assert (G2 : getr rc0 2 = getr regs 2)
      by (apply (df_reg_atom _ _ _ _ _ 2%nat Q2); cbn [ew ewset Nat.eqb]; exact (EE 2%nat 2%bv eq_refl)).
    assert (G3 : getr rc0 3 = getr regs 3)
      by (apply (df_reg_atom _ _ _ _ _ 3%nat Q3); cbn [ew ewset Nat.eqb]; exact (EE 3%nat 3%bv eq_refl)).
    assert (G4 : getr rc0 4 = getr regs 4)
      by (apply (df_reg_atom _ _ _ _ _ 4%nat Q4); cbn [ew ewset Nat.eqb]; exact (EE 4%nat 4%bv eq_refl)).
    assert (G8 : getr rc0 8 = getr regs 8)
      by (apply (df_reg_atom _ _ _ _ _ 8%nat Q8); cbn [ew ewset Nat.eqb]; exact (EE 8%nat 8%bv eq_refl)).
    assert (HxL : Z.of_nat (length (hs_W h1)) = hs_npartial h1) by exact (df_hsW_len RG HGSB h1 Anp Apj).
    refine (df_lp_call_xR cx Hp kr ly1 S1 Hp1 k1 W mc _ rc0 (getr rc0 1) (hs_expected h1) (hs_W h1) (hs_partial h1)
      APARTIAL (df_kr2 (hs_expected h1) (Z.of_nat (length (hs_W h1))) tl kr) Q
      HB HJ _ _ _ eq_refl _ _ _ _ _ _ _ PPB PNE _ _ PNZ PLEN PGR PLIVE PMO PFP PRM PCNT _).
    { unfold spZ in R2 |- *. rewrite G2. exact R2. }
    { rewrite G3, R3. exact Hgp0. }
    { rewrite G4, R4. exact Htp0. }
    { rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { rewrite T1, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_B_ok. lia. }
    { unfold s0Z. rewrite G8, R8. unfold w64. pose proof asan_consts as (C1 & _).
      assert (Hd : 0 <= (rg_s RG + 4) / 8 <= rg_s RG + 4)
        by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; clear - HGlo; lia).
      rewrite unsigned_lit_small by (clear - Hd HGlo HGhi; unfold ASRC in *; lia).
      clear - Hd HGlo HGhi C1. unfold ASRC in *. lia. }
    { rewrite Q10. unfold w64. apply df_denc; [cbn [ew ewset Nat.eqb]; exact E23 | clear - HAr; lia]. }
    { rewrite Q11. unfold w64. apply df_den0. cbn [ew ewset Nat.eqb]. exact E32. }
    { rewrite Q12, HxL. unfold w64. apply df_den0. cbn [ew ewset Nat.eqb]. exact E33. }
    { apply (alist_at_kept B ly1 S1 W m ly1 S1 W mc _ _ _ PAL).
      - apply ((df_pu_alist_kept B RG) ly1 S1 W W m mc _ _ _ PAL).
        + intros a Ha. apply ((df_keep_of_meq RG) W m mc (df_Pg (dHA RG cx)) MEQ PR a);
            [clear - Ha HAr; lia | unfold df_Pg; clear - Ha; lia].
        + intros p n a Hpn Ha.
          destruct (df_heap_np_x ly1 S1 Hp1 W m md (dHA RG cx) p n a HAR0
            ((df_alist_blks_in B) ly1 S1 W m _ _ _ PAL (p, n) Hpn) Ha HAlo HAhi) as (F1 & F2).
          exact ((df_keep_of_meq RG) W m mc (df_Pg (dHA RG cx)) MEQ PR a F1 F2).
      - intros bb Hbb. exact ((df_alist_blks_in B) ly1 S1 W m _ _ _ PAL bb Hbb). }
    { rewrite HxL. clear - Anp HrqA. unfold APARTIAL in *. lia. }
    { apply (garr8_frame SEGS (mrestrict (w_H W) m) (mrestrict (w_H W) mc) _ _ PG8).
      intros a Ha. apply (mbyte_of_aview SEGS). unfold bzs in Ha. rewrite length_map, HxL in Ha.
      destruct (df_heap_np_x ly1 S1 Hp1 W m md (dHA RG cx) (hs_partial h1) APARTIAL a HAR0 PPB
        ltac:(clear - Ha Anp HrqA; unfold APARTIAL in *; lia) HAlo HAhi) as (F1 & F2).
      exact (proj1 ((df_keep_of_meq RG) W m mc (df_Pg (dHA RG cx)) MEQ PR a F1 F2)). }
    intros W2 ly2 S2 Hp2 kk regs2 m2 md2 l2 d HJ2 HAP KB KI KE KF HROM2 HPK2 HFR2 HL2 Hrecs Hcap Hv HPERM HMO HRM2.
    (* ---- back at 0x834f4: drain's state after the call ---- *)
    assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
    assert (HDF : DRAIN_FRAME = 336) by reflexivity.
    pose proof asan_consts as (C1 & _).
    rewrite T1.
    jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) m2) HAP [0; 1]%nat HS2.
    match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb];
          rewrite U2; intros a Ha.
        + apply (mbyte_of_aview SEGS). apply (proj1 (KF a ltac:(unfold spZ in *; clear - Ha R2 HDF; lia))).
        + exfalso. clear - Ha. lia.
      - assert (KG : forall a, dHA RG cx + 40 <= a < dHA RG cx + 60 -> abyte_kept W mc W2 m2 a).
        { intros a Ha.
          assert (Hg : rg_s RG <= a < rg_s RG + 4 * ASRC) by (rewrite HAe in Ha; unfold ASRC in *; clear - Ha Hj; lia).
          destruct ((df_pu_gs B RG HRGD) a Hg) as (HgG & Hne).
          destruct (HG a HgG) as (Hi & Ho & _).
          apply (KI a Hi Ho Hne (PSTG a Hg)). clear - Ha. lia. }
        split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb];
          rewrite U23; intros a Ha.
        + apply (mbyte_of_aview SEGS). exact (proj1 (KG a Ha)).
        + intros Hw. exact (proj2 (KG a ltac:(clear - Ha; lia)) Hw). }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    lazymatch type of HS with st_ok_pi _ _ (havoc ?Ex 40 ?lc) _ _ =>
      assert (OLDc : forall n, (n < 40)%nat -> ew (havoc Ex 40 lc) n = ew Ex n)
        by (intros n Hn; apply YN3v.ew_havoc_old; exact Hn);
      assert (HEIc : img_env VAL A_LIM (havoc Ex 40 lc)) by (apply img_env_havoc; [assumption | cbv; lia]);
      remember (havoc Ex 40 lc) as Ec eqn:HEc in HS, OLDc, HEIc
    end.
    clear HEc.
    assert (EEc : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ec n = getr regs r).
    { intros n r Hn'. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
      rewrite OLDc by lia. rewrite !ew_ewset_other by lia. exact (EE n r Hn'). }
    assert (E23c : ew Ec 23 = Z_to_bv 64 (dHA RG cx)) by (rewrite (EEc 23%nat 23%bv eq_refl), R23; reflexivity).
    assert (E21c : ew Ec 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEc 21%nat 21%bv eq_refl), R21; reflexivity).
    assert (U23c : bv_unsigned (ew Ec 23) = dHA RG cx) by (rewrite E23c; apply unsigned_lit_small; clear - HAr; lia).
    pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
    assert (SHOKc : sh_ok SEGS df_Bx [mkSHE 23 0 96] Ec (mrestrict (w_H W2) m2)).
    { unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
      eapply shent_ok_of_range.
      - exact (azs_range_addressable_x B ARx LAWS ly2 S2 Hp2 W2 m2 md2 (rg_s RG) (4 * ASRC) HAR2 HGSZ).
      - unfold df_Bx. apply U_atom; [exact E21c | unfold SHADOW_OFF; lia].
      - apply U_atom; [exact E23c | clear - HAr; lia].
      - clear - HAlo. lia.
      - clear - HAhi. unfold ASRC in *. lia.
      - intros x Hx. change (Z.min 0 96) with 0 in Hx. change (Z.max 0 96) with 96 in Hx.
        unfold SHADOW_OFF. clear - Hx HAr. lia. }
    clear SHOK.
    assert (MEQc : forall x : word, ~ df_Pg (dHA RG cx) (bv_unsigned x) ->
      mrestrict (w_H W2) m2 x = mrestrict (w_H W2) m2 x) by (intros; reflexivity).
    assert (PRc : forall a, apresent (w_H W2) m2 a -> apresent (w_H W2) m2 a) by (intros a Ha; exact Ha).
    paj_run_to_tok_xR RUNTOR HS HJ2 SHOKc DFspan A_df_tail. { df_awr U23c HAe. }
    df_track m2 MEQc PRc U23c.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
    pmkst HS.
    refine (df_tail_xR cx Hp kr s1 D k p0 W2 _ _ _ Q _ _ _ Hnext Hend).
    * df_regs_tac HS HR EEc E23c E21c HAr R20 R27 R22.
    * exists ly2, S2, Hp2, kk, e1. eexists.
      refine (df_close_push_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl ly2 S2 Hp2 kk W2 _ _ l2 d HB HCt Hb Hov0
        HJ2 _ _ _ _ _ _ HFR2 _ _ _ Hrecs Hcap Hv HPERM HMO HRM2).
      -- intros p n i Hin Hne Hi.
        destruct (df_heap_np_x ly1 S1 Hp1 W m md (dHA RG cx) p n (p + i) HAR0 Hin ltac:(clear - Hi; lia) HAlo HAhi)
          as (F1 & F2).
        apply (df_bk_trans W W2 W2 m m2 _ (p + i)).
        ++ apply (df_bk_trans W W W2 m mc m2 (p + i)).
           ** exact ((df_keep_of_meq RG) W m mc (df_Pg (dHA RG cx)) MEQ PR (p + i) F1 F2).
           ** exact (KB p n i Hin Hne Hi).
        ++ exact ((df_keep_of_meq RG) W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc (p + i) F1 F2).
      -- intros a Hi Ho He Hpst H48 H64.
        destruct (df_img_np (dHA RG cx) a Hi H48) as (F1 & F2).
        apply (df_bk_trans W W2 W2 m m2 _ a).
        ++ apply (df_bk_trans W W W2 m mc m2 a).
           ** exact ((df_keep_of_meq RG) W m mc (df_Pg (dHA RG cx)) MEQ PR a F1 F2).
           ** exact (KI a Hi Ho He Hpst H64).
        ++ exact ((df_keep_of_meq RG) W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a F1 F2).
      -- intros a Ha.
        assert (Hcase : (0 <= a < 2 ^ 64 /\ ~ (rg_s RG <= a < rg_s RG + 4 * ASRC)) /\
          ((as_errno B <= a < as_errno B + 4) \/
           (in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)))).
        { destruct Ha as [Hc | [Hc | [Hc | He]]].
          - destruct ((df_cell_facts B RG HGO HRGD) a (or_introl Hc)) as (F1 & F2 & F3 & F4 & F5).
            split; [split; assumption | right; split; [exact F3 | split; assumption]].
          - destruct ((df_cell_facts B RG HGO HRGD) a (or_intror (or_introl Hc))) as (F1 & F2 & F3 & F4 & F5).
            split; [split; assumption | right; split; [exact F3 | split; assumption]].
          - destruct ((df_cell_facts B RG HGO HRGD) a (or_intror (or_intror Hc))) as (F1 & F2 & F3 & F4 & F5).
            split; [split; assumption | right; split; [exact F3 | split; assumption]].
          - destruct ((df_errno_facts B RG HG HRGD) a He) as (F1 & F2 & F3).
            split; [split; assumption | left; exact He]. }
        destruct Hcase as ((F1 & F2) & Hcase).
        assert (F3 : ~ df_Pg (dHA RG cx) a)
          by (unfold df_Pg; rewrite HAe; unfold ASRC in *; clear - F2 Hj; lia).
        apply (df_bk_trans W W2 W2 m m2 _ a).
        ++ apply (df_bk_trans W W W2 m mc m2 a).
           ** exact ((df_keep_of_meq RG) W m mc (df_Pg (dHA RG cx)) MEQ PR a F1 F3).
           ** destruct Hcase as [He | (Hi & Ho & He)]; [exact (KE a He)|].
              apply (KI a Hi Ho He (df_cell_pst a Ha)). rewrite HAe. unfold ASRC in *. clear - F2 Hj. lia.
        ++ exact ((df_keep_of_meq RG) W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a F1 F3).
      -- intros a Ha.
        assert (F1 : 0 <= a < 2 ^ 64) by (unfold spZ in *; clear - Ha Hsp R2 HDF C1; lia).
        assert (F3 : ~ df_Pg (dHA RG cx) a) by (unfold df_Pg, spZ in *; clear - Ha Hsp R2 HDF C1 HAr; lia).
        apply (df_bk_trans W W2 W2 m m2 _ a).
        ++ apply (df_bk_trans W W W2 m mc m2 a).
           ** exact ((df_keep_of_meq RG) W m mc (df_Pg (dHA RG cx)) MEQ PR a F1 F3).
           ** exact (KF a Ha).
        ++ exact ((df_keep_of_meq RG) W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a F1 F3).
      -- intros a Ha.
        assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
        assert (H48 : ~ (dHA RG cx + 48 <= a < dHA RG cx + 60)).
        { intros Hg. apply (HGR a); [|exact Ha].
          unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
          rewrite HAe in Hg. unfold ASRC in *. clear - Hg Hj. lia. }
        destruct (df_img_np (dHA RG cx) a Hi H48) as (F1 & F2).
        rewrite (proj1 ((df_keep_of_meq RG) W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a F1 F2)). exact (HROM2 a Ha).
      -- intros a Hi Ho He Hpr. apply PRc. apply (HPK2 a Hi Ho He). apply PR. exact Hpr.
      -- apply (alist_at_kept B ly2 S2 W2 m2 ly2 S2 W2 _ _ _ _ HL2).
        ++ apply ((df_pu_alist_kept B RG) ly2 S2 W2 W2 m2 _ _ _ _ HL2).
           ** intros a Ha. apply ((df_keep_of_meq RG) W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a);
                [clear - Ha HAr; lia | unfold df_Pg; clear - Ha; lia].
           ** intros p n a Hpn Ha.
              destruct (df_heap_np_x ly2 S2 Hp2 W2 m2 md2 (dHA RG cx) p n a HAR2
                ((df_alist_blks_in B) ly2 S2 W2 m2 _ _ _ HL2 (p, n) Hpn) Ha HAlo HAhi) as (F1 & F2).
              exact ((df_keep_of_meq RG) W2 m2 _ (df_Pg (dHA RG cx)) MEQc PRc a F1 F2).
        ++ intros bb Hbb. exact ((df_alist_blks_in B) ly2 S2 W2 m2 _ _ _ HL2 bb Hbb).
      -- df_v (dHA RG cx) U23c 48 8%N (SLit 0) 0; [reflexivity | cbn; lia].
      -- df_v (dHA RG cx) U23c 56 4%N (SLit 0) 0; [reflexivity | cbn; lia].
    * clear - Hk. lia.
- (* 0x8349c fall: b <> 0 *)
  rewrite branch_eq_U, df_U0 in Hc. df_Uat Hc 35%nat b E35 Rb. apply Z.eqb_neq in Hc. rename Hc into Hb0.
  paj_run_tok_xR RUNR HS HJ SHOK DFspan. { df_awr U23 HAe. }
  df_track m MEQ PR U23.
  psrr_branch_tok RUNR BRR HS SHOK DFspan.
  + (* 0x834a0 taken: overlong <> 0, skip *)
    rewrite branch_ne_U, df_U0 in Hc. df_Uat Hc 34%nat (hs_overlong h1) E34 Rov.
    pose proof (df_ovl_nz _ Aovl Hc) as Hov1. clear Hc.
    df_leaf_runR HS HJ SHOK U23 HAe m MEQ PR 1%nat.
    refine (df_finish_nw_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b _ _ _ (hs_npartial h1) (hs_overlong h1) Q HB
      _ Hk
      HC Hb HJ ((df_keep_of_meq RG) W m _ (df_Pg (dHA RG cx)) MEQ PR) PR _ _ _ _ _ _ _ Hnext Hend).
    * df_regs_tac HS HR EE E23 E21 HAr R20 R27 R22.
    * df_v (dHA RG cx) U23 48 8%N (SOff 33 0) (hs_npartial h1);
        [apply df_den0; cbn [ew ewset Nat.eqb]; exact E33 | cbn; clear - Rnp; lia].
    * df_v (dHA RG cx) U23 56 4%N (SOff 34 0) (hs_overlong h1);
        [apply df_den0; cbn [ew ewset Nat.eqb]; exact E34 | cbn; rewrite Hov1; lia].
    * exact Anp.
    * right. exact Hov1.
    * rewrite (df_step_skip h1 b Hb0 Hov1). apply df_state_skip; reflexivity.
    * rewrite (df_step_skip h1 b Hb0 Hov1). reflexivity.
    * exact AnoW.
  + rewrite branch_ne_U, df_U0 in Hc. df_Uat Hc 34%nat (hs_overlong h1) E34 Rov.
    pose proof (df_ovl_z _ Hc) as Hov0. clear Hc.
    paj_run_tok_xR RUNR HS HJ SHOK DFspan. { df_awr U23 HAe. }
    df_track m MEQ PR U23.
    psrr_branch_tok RUNR BRR HS SHOK DFspan.
    * (* 0x834b8 taken: npartial <> 6000, add *)
      rewrite branch_ne_U, df_U6000 in Hc. df_Uat Hc 33%nat (hs_npartial h1) E33 Rnp.
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hnp6.
      assert (HnpA : hs_npartial h1 <> APARTIAL) by (unfold APARTIAL; exact Hnp6).
      assert (Hnp : 0 <= hs_npartial h1 < APARTIAL) by (clear - Anp HnpA; lia).
      pose proof (df_cutjh_journal_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 HC) as HJ0.
      assert (HAR0 : ARx ly1 S1 Hp1 W m md) by (eapply ajournal_gx_AR_xR; exact HJ0).
      destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W m md _ _ HAR0 Apb) as (_ & Hp4096 & Hpceil & Happ & Hppres & _).
      pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & HrqA).
      pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
      pose proof (df_cutjh_sp_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 regs HR HC) as Hsp.
      destruct (df_src_byte_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b HC Hb)
        as (q & qn & Hqin & _ & Hqne & Hq1 & Hq2 & _ & _).
      destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W m md q qn HAR0 Hqin) as (_ & Hq4096 & Hqceil & _).
      pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSAME & _).
      pose proof HSAME as (_ & _ & _ & _ & _ & _ & _ & Hpsame & _).
      set (pn := hs_partial h1 + hs_npartial h1) in *.
      assert (Hin_pn : hs_partial h1 <= pn < hs_partial h1 + req_size APARTIAL) by (unfold pn; clear - Hnp HrqA; lia).
      assert (Hpn64 : 4096 <= pn /\ pn + 1 <= alloc_ceiling /\ 0 <= pn < 2 ^ 64)
        by (clear - Hin_pn Hp4096 Hpceil ACL; lia).
      assert (Hpngs : pn + 1 <= dHA RG cx + 40 \/ dHA RG cx + 60 <= pn).
      { assert (Hin' : hs_partial h1 <= pn < hs_partial h1 + APARTIAL) by (unfold pn; clear - Hnp; lia).
        pose proof (df_blk_gs_x ly1 S1 Hp1 W m md _ _ _ HAR0 Apb Hin') as Hng.
        rewrite HAe. unfold ASRC in *.
        destruct (Z_lt_le_dec pn (rg_s RG)) as [Hlt|Hge]; [left; clear - Hlt; lia|].
        destruct (Z_lt_le_dec pn (rg_s RG + 4 * 96)) as [Hlt2|Hge2]; [exfalso; apply Hng; split; assumption|].
        right. clear - Hge2 Hj. lia. }
      assert (Hpnsrc : pn + 1 <= p0 + Z.of_nat k \/ p0 + Z.of_nat k + 1 <= pn).
      { pose proof (df_blk_out_rq_x ly1 S1 Hp1 W m md _ _ q qn _ HAR0 Apb Hqin (not_eq_sym Hqne) Hin_pn) as Hno.
        destruct (Z_lt_le_dec pn (p0 + Z.of_nat k)) as [Hlt|Hge]; [left; clear - Hlt; lia|right].
        destruct (Z.eq_dec pn (p0 + Z.of_nat k)) as [Heq|Hne]; [|clear - Hge Hne; lia].
        exfalso. apply Hno. clear - Heq Hq1 Hq2. lia. }
      assert (U36 : bv_unsigned (ew E 36) = pn) by (rewrite E36; apply unsigned_lit_small; tauto).
      assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
      assert (U26 : bv_unsigned (ew E 26) = p0 + Z.of_nat k).
      { rewrite (EE 26%nat 26%bv eq_refl), R26. unfold w64. apply unsigned_lit_small.
        clear - Hq1 Hq2 Hq4096 Hqceil ACL. pose proof (req_size_pos qn) as Hrq. lia. }
      lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
        assert (AF36 : afact_ok Ex 36 df_HEAPF);
        [ unfold afact_ok, df_HEAPF; cbn [af_lo af_hi af_al2 ew ewset Nat.eqb]; rewrite U36;
          rewrite Z.pow_0_r, Z.mod_1_r; pose proof asan_consts as (C1 & _);
          clear - Hpn64 C1; repeat match goal with |- _ /\ _ => split end; (exact I || lia) |];
        assert (AL36 : sv_denot Ex (SAlu ALU_ADD (SOff 32 0) (SOff 33 0)) = sv_denot Ex (SOff 36 0));
        [ apply ((df_alias36 RG) Ex (hs_partial h1) (hs_npartial h1)); cbn [ew ewset Nat.eqb];
          [exact E32 | exact E33 | exact E36 | clear - Hp4096 Hpceil ACL HrqA; unfold APARTIAL in *; lia | exact Rnp | tauto] |]
      end.
      pose proof (st_ok_pi_add_fact _ _ _ 36 df_HEAPF HS AF36) as HS1. clear HS. rename HS1 into HS. norm_ss HS.
      pose proof (st_ok_pi_add_alias _ _ _ _ _ HS AL36) as HS1. clear HS. rename HS1 into HS. norm_ss HS.
      lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
        assert (RG36 : region_ok SEGS Ex (ms_mem (restrict (w_H W) msx)) df_r36);
        [ unfold region_ok, df_r36;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict
            ew ewset Nat.eqb]; rewrite U36;
          split; [clear - Hpn64; lia|]; split; [clear - Hpn64; lia|]; split; [|apply Forall_nil];
          intros o Ho; apply (apresent_writable SEGS); replace (pn + o) with pn by (clear - Ho; lia);
          apply PR; exact (proj1 (Hppres pn Hin_pn)) |];
        assert (DJ36 : all_disjoint Ex df_r36 (ss_mem ssx));
        [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
            let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, df_r36;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val ew ewset Nat.eqb]; rewrite U36, U2, U23, U26;
          split; [left; clear - Hsp Hpn64; lia|]; split; [clear - Hpngs; lia|]; split; [clear - Hpnsrc; lia|];
          exact I |]
      end.
      pose proof (st_ok_pi_add_region _ _ _ df_r36 HS eq_refl RG36 DJ36) as HS1. clear HS. rename HS1 into HS.
      norm_ss HS.
      lazymatch type of SHOK with sh_ok _ _ _ ?Ex ?mx =>
        assert (SHOK2 : sh_ok SEGS df_Bx (mkSHE 36 0 1 :: df_SH) Ex mx);
        [ unfold sh_ok; apply Forall_cons; [|exact SHOK];
          eapply (shent_ok_of_range SEGS (w_H W) _ Ex df_Bx 36%nat pn 1 pn 0 1);
          [ eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W _ _ (hs_partial h1) APARTIAL);
            [ exact (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) | exact Apb
            | clear - Hin_pn; lia | clear - Hin_pn; lia ]
          | unfold df_Bx; apply U_atom; [cbn [ew ewset Nat.eqb]; exact E21 | unfold SHADOW_OFF; lia]
          | apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite E36; reflexivity | tauto]
          | lia | lia
          | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia; revert Happ Hin_pn Hx; clear;
            unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; lia ] |]
      end.
      clear SHOK. rename SHOK2 into SHOK.
      pose proof (df_meq_weak (w_H W) m _ (df_Pg (dHA RG cx)) (df_Pa (dHA RG cx) pn) (fun a Ha => or_introl Ha) MEQ)
        as MEQ2.
      clear MEQ.
      paj_run_to_tok_xR RUNTOR HS HJ SHOK DFspan A_df_tail.
      { lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?bl0 ?blc ?ly ?own =>
          let rs2 := eval vm_compute in rs in change (awr_ok_x E rs2 G XO OUT STK sp0 FP bl0 blc ly own) end.
        apply awr_ok_x_cons.
        - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Ha. rewrite U36 in Ha.
          left. split; [|clear - Ha; lia].
          unfold awr_byte. right. left. split.
          + exists (hs_partial h1, hs_partial h1 + req_size APARTIAL). split; [|cbn [fst snd]; clear - Ha Hin_pn; lia].
            unfold dFP, dr_fp. right. unfold ablocks_fp.
            apply (in_map (fun b0 => (fst b0, fst b0 + req_size (snd b0))) _ (hs_partial h1, APARTIAL)).
            apply in_or_app. right. apply in_or_app. left. unfold asrc_blks. left. rewrite Hpsame. reflexivity.
          + exists (hs_partial h1), APARTIAL. split; [exact Apb | clear - Ha Hin_pn; lia].
        - df_awr U23 HAe. }
      lazymatch goal with
      | HF : frame_of ?Ex ?rs (mrestrict ?Hh ?mc) (mrestrict ?Hh ?mn),
        HGr : mem_grows (mrestrict ?Hh ?mc) (mrestrict ?Hh ?mn) |- _ =>
        pose proof (df_meq_step Ex rs Hh m mc mn (df_Pa (dHA RG cx) pn) MEQ2 HF
          ltac:(intros a Ha; pose proof ((df_wrange RG HGSB) Ex rs a ltac:(vm_compute; reflexivity) Ha) as Hw;
                cbn [ew ewset Nat.eqb] in Hw; rewrite U23, U36 in Hw; exact Hw)) as MEQ3;
        assert (PR3 : forall a, apresent Hh m a -> apresent Hh mn a)
          by (intros a Ha; exact (apresent_grows Hh mc mn a HGr (PR a Ha)))
      end.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RGb. cbn [ms_mem restrict] in RGb.
      pmkst HS.
      refine (df_finish_add_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b _ _ _ Q HB _ Hk HC Hb Hb0 Hov0 HnpA HJ
        (fun a Ha H1 H2 => (df_keep_of_meq RG) W m _ (df_Pa (dHA RG cx) pn) MEQ3 PR3 a Ha
           (fun H => match H with or_introl H' => H1 H' | or_intror H' => H2 H' end)) PR3 _ _ _ Hnext Hend).
      -- df_regs_tac HS HR EE E23 E21 HAr R20 R27 R22.
      -- df_v (dHA RG cx) U23 48 8%N (SOff 33 1) (hs_npartial h1 + 1);
           [apply df_denc; [cbn [ew ewset Nat.eqb]; exact E33 | exact Rnp] | cbn; clear - Hnp; unfold APARTIAL in *; lia].
      -- df_v (dHA RG cx) U23 56 4%N (SOff 34 0) 0;
           [apply df_den0; cbn [ew ewset Nat.eqb]; rewrite E34, Hov0; reflexivity | cbn; lia].
      -- unfold arm. rewrite <- (Z.add_0_r (hs_partial h1 + hs_npartial h1)).
         eapply (field_of_region _ _ 36%nat pn _ _ _ _ _ 0 1%N (SOff 35 0) b RGb);
           [cbn [ew ewset Nat.eqb]; exact U36 | cbn [In]; df_inc | apply df_den0; cbn [ew ewset Nat.eqb]; exact E35
           | cbn; clear - Hb8; lia | cbn; lia].
    * (* 0x834b8 fall: npartial = 6000, long *)
      rewrite branch_ne_U, df_U6000 in Hc. df_Uat Hc 33%nat (hs_npartial h1) E33 Rnp.
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hnp6.
      assert (HnpA : hs_npartial h1 = APARTIAL) by (unfold APARTIAL; exact Hnp6).
      df_leaf_runR HS HJ SHOK U23 HAe m MEQ PR 1%nat.
      refine (df_finish_nw_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b _ _ _ (hs_npartial h1) 1 Q HB _ Hk
        HC Hb HJ ((df_keep_of_meq RG) W m _ (df_Pg (dHA RG cx)) MEQ PR) PR _ _ _ _ _ _ _ Hnext Hend).
      -- df_regs_tac HS HR EE E23 E21 HAr R20 R27 R22.
      -- df_v (dHA RG cx) U23 48 8%N (SOff 33 0) (hs_npartial h1);
           [apply df_den0; cbn [ew ewset Nat.eqb]; exact E33 | cbn; clear - Rnp; lia].
      -- df_v (dHA RG cx) U23 56 4%N (SLit 1) 1; [reflexivity | cbn; lia].
      -- exact Anp.
      -- right. reflexivity.
      -- rewrite ((df_step_long RG HGSB) h1 b Hb0 Hov0 HnpA Apj). apply df_state_long; reflexivity.
      -- rewrite ((df_step_long RG HGSB) h1 b Hb0 Hov0 HnpA Apj). reflexivity.
      -- exact AnoW.
Qed.

Lemma df_ddata_nth_xR : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1,
df_cutjh_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> Z.of_nat k < dnum s1 ->
exists b, nth_error (ddata s1) k = Some b.
Proof.
intros cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 HC Hk.
destruct HC as (tl & out1 & ev1 & LB1 & spent & jb & a & v & rs & r0 & rs0 &
  _ & Hpend & _ & _ & _ & HMEM & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpendm & Hoff & _).
pose proof HMEM as (_ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _).
pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ahead & _).
assert (Hoff0 : 0 <= hs_off h1).
{ clear - Ahead Hpend. destruct Ahead as [(Hn & _) | (r & rs' & Hr & Ho)].
  { rewrite Hpend in Hn. discriminate. }
  lia. }
destruct (nth_error (ddata s1) k) as [b|] eqn:Hb; [exists b; reflexivity|].
exfalso. apply nth_error_None in Hb.
unfold ddata in Hb. rewrite length_firstn, length_skipn in Hb.
unfold dnum in Hb, Hk. rewrite <- Hoff in Hb, Hk. revert Hb Hk Hoff0. clear. intros. lia.
Qed.

Lemma df_feed_step_xR : forall cx Hp kr s1 D k W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D k W1 c1 ->
Z.of_nat k < dnum s1 ->
(forall W2 c2, DRB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S k) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, DE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
Proof.
intros cx Hp kr s1 D k W1 c1 HB HRB Hk Hnext Hend.
destruct (df_DRB_open_xR cx Hp kr s1 D k W1 c1 HRB) as (regs1 & m1 & md1 & p0 & -> & HR & _ & HCut).
destruct HCut as (ly1 & S1 & Hp1 & k1 & e1 & h1 & HC).
destruct (df_ddata_nth_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W1 m1 md1 e1 h1 HC Hk) as (b & Hb).
exact (df_body_xR cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W1 regs1 m1 md1 e1 h1 b _ HB HR Hk HC Hb Hnext Hend).
Qed.

Theorem dr_feed_p_xR : dr_feed_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold dr_feed_stmt_xR. intros cx Hp kr s1 D k W1 c1 HB HRB Hnext Hend.
exact (df_feed_step_xR cx Hp kr s1 D k W1 c1 HB HRB (df_DRB_bytes_xR cx Hp kr s1 D k W1 c1 HRB) Hnext Hend).
Qed.

Theorem dr_feeds_p_xR : dr_feeds_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold dr_feeds_stmt_xR, dr_feeds_concl_x. intros FEED cx Hp kr s1 D k W1 c1 HB HRB HDE.
(* the loop runs at most dnum s1 - k more turns; carry that as an upper bound on the fuel *)
assert (HM : exists m : nat, (Z.to_nat (dnum s1) - k <= m)%nat)
  by (exists (Z.to_nat (dnum s1) - k)%nat; apply Nat.le_refl).
destruct HM as (m & Hm). revert k W1 c1 HRB Hm.
induction m as [|m IH]; intros k W1 c1 HRB Hm;
apply (FEED cx Hp kr s1 D k W1 c1 HB HRB); try exact HDE; intros W2 c2 HRB2;
pose proof (df_DRB_bytes_xR cx Hp kr s1 D (S k) W2 c2 HRB2) as Hle;
rewrite Nat2Z.inj_succ in Hle.
- (* no byte left: a cut at S k would need S k < dnum s1 *)
  exfalso. revert Hm Hle. clear. intros Hm Hle. lia.
- apply (IH (S k) W2 c2 HRB2). revert Hm Hle. clear. intros Hm Hle. lia.
Qed.

End wR.

(* ---- the strict pieces: each is its R twin at R := @wle SEGS ---- *)
Lemma df_DRB_bytes_x : forall cx Hp kr s1 D k W1 c1,
DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D k W1 c1 -> Z.of_nat k < dnum s1.
Proof.
eapply (df_DRB_bytes_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Definition df_cutjt_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (p0 : Z)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (k1 : Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model)
(e1 : rentry) (h1 : hsrc) (tl : dtrace) : Prop :=
df_cutjt_xR (@wle SEGS) cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W1 m1 md1 e1 h1 tl.

Definition df_cutjh_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (p0 : Z)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (k1 : Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model)
(e1 : rentry) (h1 : hsrc) : Prop :=
df_cutjh_xR (@wle SEGS) cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W1 m1 md1 e1 h1.

Definition df_cutj_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (p0 : Z)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (k1 : Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model)
: Prop :=
df_cutj_xR (@wle SEGS) cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W1 m1 md1.

Definition df_cut_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (p0 : Z)
(W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) : Prop :=
df_cut_xR (@wle SEGS) cx Hp kr s1 D k p0 W1 m1 md1.

Lemma df_DRB_open_x : forall cx Hp kr s1 D k W1 c1, DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D k W1 c1 ->
exists regs1 m1 md1 p0, c1 = cfg_at SEGS (BASE + A_dr_feed) regs1 m1 md1 /\ (df_regs RG) cx s1 p0 k regs1 /\
Z.of_nat k < dnum s1 /\ df_cut_x cx Hp kr s1 D k p0 W1 m1 md1.
Proof.
eapply (df_DRB_open_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_DRB_close_x : forall cx Hp kr s1 D k p0 W1 regs1 m1 md1,
(df_regs RG) cx s1 p0 k regs1 -> Z.of_nat k < dnum s1 -> df_cut_x cx Hp kr s1 D k p0 W1 m1 md1 ->
DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D k W1 (cfg_at SEGS (BASE + A_dr_feed) regs1 m1 md1).
Proof.
eapply (df_DRB_close_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* at k = dnum s1 every byte is fed: the rest is DE's body, with the round's pushes all done *)
Lemma df_DE_close_x : forall cx Hp kr s1 D kk p0 W1 regs1 m1 md1,
(df_regs RG) cx s1 p0 kk regs1 -> df_cut_x cx Hp kr s1 D (Z.to_nat (dnum s1)) p0 W1 m1 md1 ->
DE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W1 (cfg_at SEGS (BASE + A_dr_fed) regs1 m1 md1).
Proof.
eapply (df_DE_close_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_dmem_rebuild_x : forall cx Hp ly S Hp1 W m md k e h s out ev sent LB ly' S' Hp' W' m' md' k' h',
DMEM_x B PST ARx RG cx Hp ly S Hp1 W m md k e h s out ev sent LB ->
AJGX (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly' S' Hp' W' m' md' k' ->
rom_view SEGS W' m' ->
apres_kept B W m W' m' -> frames S' = frames S ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
(forall a, dxSA cx <= a < dxSA cx + AENT -> abyte_kept W m W' m' a) ->
akept W m W' m' (aentry_fp e) ->
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= a < dHA RG cx + ASRC) ->
   abyte_kept W m W' m' a) ->
akept W m W' m' (aout_fp B RG (drain_b_c.ds_ocap s) out) ->
asrc_at B ly' S' W' m' (dHA RG cx) h' ->
Permutation (ablocks B ly' S')
  ((dxG cx, ATABLE) :: aentry_blks e ++ asrc_blks h' ++ aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) ->
DMEM_x B PST ARx RG cx Hp ly' S' Hp' W' m' md' k' e h' s out ev sent LB.
Proof.
eapply (df_dmem_rebuild_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_cutj_journal_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md,
df_cutj_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md ->
AJGX (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W m md k1.
Proof.
eapply (df_cutj_journal_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_cutj_mem_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md m' md',
df_cutj_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md ->
(forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
AJGX (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W m' md' k1 ->
df_cutj_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m' md'.
Proof.
eapply (df_cutj_mem_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_cutj_dnum_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md,
df_cutj_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md -> 0 < dnum s1 <= 16384.
Proof.
eapply (df_cutj_dnum_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* data byte k is the byte at p0 + k, in the head pending text's block (a block other than h->partial) *)
Lemma df_src_byte_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b,
df_cutjh_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
exists q qn, In (q, qn) (ablocks B ly1 S1) /\ In (q, qn) (asrc_blks h1) /\ q <> hs_partial h1 /\
q <= p0 + Z.of_nat k /\ p0 + Z.of_nat k + 1 <= q + req_size qn /\
val_mem SEGS (arm W m) (p0 + Z.of_nat k) 1 b /\ 0 <= b < 256.
Proof.
eapply (df_src_byte_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* the symbolic state at the loop head and its shadow entries, from the cut *)
Lemma df_entry_full_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W regs m md e1 h1 b,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> (df_regs RG) cx s1 p0 k regs -> Z.of_nat k < dnum s1 ->
df_cutjh_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (df_extra (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b))) df_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_feed)) m (seg_rom SEGS))) /\
sh_ok SEGS df_Bx df_SH (Eimg (Ereg regs (df_extra (hs_partial h1) (hs_npartial h1) (hs_overlong h1) b)))
  (mrestrict (w_H W) m).
Proof.
eapply (df_entry_full_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_tail_x : forall cx Hp kr s1 D k p0 W regs m md Q,
(df_regs RG) cx s1 p0 k regs -> df_cut_x cx Hp kr s1 D (S k) p0 W m md -> Z.of_nat (S k) <= dnum s1 ->
(forall W2 c2, DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S k) W2 c2 -> SRr SEGS W2 c2 Q) ->
(forall W2 c2, DE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W2 c2 -> SRr SEGS W2 c2 Q) ->
SRr SEGS W (cfg_at SEGS (BASE + A_df_tail) regs m md) Q.
Proof.
eapply (df_tail_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* skip, long, add, reset: the byte b pushes no line *)
Lemma df_close_local_x : forall cx hp kr s1 D k p0 ly1 S1 hp1 k1 W m md e1 h1 m' md' h2 b,
DBASE_x B ARx MT RP MMAX RG cx hp kr ->
df_cutjh_x cx hp kr s1 D k p0 ly1 S1 hp1 k1 W m md e1 h1 ->
AJGX (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 hp1 W m' md' k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) ->
   ~ (hs_partial h1 <= a < hs_partial h1 + APARTIAL) -> abyte_kept W m W m' a) ->
(forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_client RG <= a < rg_client RG + 4) \/
   (rg_send_dead RG <= a < rg_send_dead RG + 1) -> abyte_kept W m W m' a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
asrc_at B ly1 S1 W m' (dHA RG cx) h2 ->
nth_error (ddata s1) k = Some b ->
hs_state h2 = fst (step (hs_state h1) b) -> snd (step (hs_state h1) b) = None ->
hs_fd h2 = hs_fd h1 -> hs_open h2 = hs_open h1 -> hs_closed h2 = hs_closed h1 -> hs_eintr h2 = hs_eintr h1 ->
hs_pending h2 = hs_pending h1 -> hs_off h2 = hs_off h1 -> hs_partial h2 = hs_partial h1 ->
hs_expected h2 = hs_expected h1 -> hs_held h2 = hs_held h1 ->
df_cutjh_x cx hp kr s1 D (S k) p0 ly1 S1 hp1 k1 W m' md' e1 h2.
Proof.
eapply (df_close_local_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_close_push_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl ly2 S2 Hp2 k2 W2 m2 md2 l2 d,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
df_cutjt_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl ->
nth_error (ddata s1) k = Some 0 -> hs_overlong h1 = 0 ->
AJGX (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 k2 ->
(forall p n i, In (p, n) (ablocks B ly1 S1) -> p <> hl_v (hs_expected h1) -> 0 <= i < req_size n ->
   abyte_kept W m W2 m2 (p + i)) ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   ~ Exists (in_zr a) PST ->
   ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) -> ~ (dHA RG cx + 64 <= a < dHA RG cx + 80) ->
   abyte_kept W m W2 m2 a) ->
(forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_client RG <= a < rg_client RG + 4) \/
   (rg_send_dead RG <= a < rg_send_dead RG + 1) \/ (as_errno B <= a < as_errno B + 4) ->
   abyte_kept W m W2 m2 a) ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W2 m2 a) ->
rom_view SEGS W2 m2 -> apres_kept B W m W2 m2 -> frames S2 = frames S1 ->
alist_at B ly2 S2 W2 m2 (dHA RG cx + 64) l2 true ->
val_mem SEGS (arm W2 m2) (dHA RG cx + 48) 8 0 -> val_mem SEGS (arm W2 m2) (dHA RG cx + 56) 4 0 ->
hl_recs l2 = hl_recs (hs_expected h1) ++ [(d, hs_W h1)] ->
hl_cap l2 = ListRep.grow_cap (hl_n (hs_expected h1)) (hl_cap (hs_expected h1)) ->
(lp_grow (hs_expected h1) = false -> hl_v l2 = hl_v (hs_expected h1)) ->
(forall rest,
 Permutation (ablocks B ly1 S1)
   ((if lp_grow (hs_expected h1) && negb (hl_cap (hs_expected h1) =? 0)
     then [(hl_v (hs_expected h1), AREC * hl_cap (hs_expected h1))] else []) ++ rest) ->
 Permutation (ablocks B ly2 S2)
   ((d, Z.of_nat (length (hs_W h1)) + 1) ::
    (if lp_grow (hs_expected h1) then [(hl_v l2, AREC * hl_cap l2)] else []) ++ rest)) ->
mo_le MT S1 S2 (lp_cost MT (hs_expected h1) (Z.of_nat (length (hs_W h1)))) ->
rp_RM RP S2 (df_kr2 (hs_expected h1) (Z.of_nat (length (hs_W h1))) tl kr) ->
df_cutjh_x cx Hp kr s1 D (S k) p0 ly2 S2 Hp2 k2 W2 m2 md2 e1
  (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
      (hs_pjunk h1) 0 0 (hs_pad h1) l2 (hs_held h1)).
Proof.
eapply (df_close_push_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* ---- The arms of the body, as runs of the symbolic engine from the loop head to the tail 0x83544. ---- *)
Lemma df_cutjh_journal_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1,
df_cutjh_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 ->
AJGX (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W m md k1.
Proof.
eapply (df_cutjh_journal_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_finish_nw_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b regs' m' md' np2 ovl2 Q,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> (df_regs RG) cx s1 p0 k regs' -> Z.of_nat k < dnum s1 ->
df_cutjh_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
AJGX (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W m' md' k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) -> abyte_kept W m W m' a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
val_mem SEGS (arm W m') (dHA RG cx + 48) 8 np2 -> val_mem SEGS (arm W m') (dHA RG cx + 56) 4 ovl2 ->
0 <= np2 <= APARTIAL -> (ovl2 = 0 \/ ovl2 = 1) ->
hs_state (HS (hs_fd h1) (hs_open h1) (hs_closed h1) (hs_eintr h1) (hs_pending h1) (hs_off h1) (hs_partial h1)
  (hs_pjunk h1) np2 ovl2 (hs_pad h1) (hs_expected h1) (hs_held h1)) = fst (step (hs_state h1) b) ->
snd (step (hs_state h1) b) = None ->
~ In (Z_to_bv 8 0) (firstn (Z.to_nat np2) (hs_pjunk h1)) ->
(forall W2 c2, DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S k) W2 c2 -> SRr SEGS W2 c2 Q) ->
(forall W2 c2, DE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W2 c2 -> SRr SEGS W2 c2 Q) ->
SRr SEGS W (cfg_at SEGS (BASE + A_df_tail) regs' m' md') Q.
Proof.
eapply (df_finish_nw_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* The end of the ordinary arm: h->partial[np] = b, h->npartial = np + 1. *)
Lemma df_finish_add_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 b regs' m' md' Q,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> (df_regs RG) cx s1 p0 k regs' -> Z.of_nat k < dnum s1 ->
df_cutjh_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
b <> 0 -> hs_overlong h1 = 0 -> hs_npartial h1 <> APARTIAL ->
AJGX (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W m' md' k1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dHA RG cx + 48 <= a < dHA RG cx + 60) -> a <> hs_partial h1 + hs_npartial h1 ->
   abyte_kept W m W m' a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
val_mem SEGS (arm W m') (dHA RG cx + 48) 8 (hs_npartial h1 + 1) ->
val_mem SEGS (arm W m') (dHA RG cx + 56) 4 0 ->
val_mem SEGS (arm W m') (hs_partial h1 + hs_npartial h1) 1 b ->
(forall W2 c2, DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S k) W2 c2 -> SRr SEGS W2 c2 Q) ->
(forall W2 c2, DE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W2 c2 -> SRr SEGS W2 c2 Q) ->
SRr SEGS W (cfg_at SEGS (BASE + A_df_tail) regs' m' md') Q.
Proof.
eapply (df_finish_add_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_cutjh_src_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1,
df_cutjh_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> asrc_at B ly1 S1 W m (dHA RG cx) h1.
Proof.
eapply (df_cutjh_src_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_push_pre_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> df_cutjt_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 tl ->
nth_error (ddata s1) k = Some 0 -> hs_overlong h1 = 0 ->
alist_at B ly1 S1 W m (dHA RG cx + 64) (hs_expected h1) true /\
In (hs_partial h1, APARTIAL) (ablocks B ly1 S1) /\ hs_partial h1 <> hl_v (hs_expected h1) /\
garr8 SEGS (mrestrict (w_H W) m) (hs_partial h1) (bzs (hs_W h1)) /\
~ In (Z_to_bv 8 0) (hs_W h1) /\ Z.of_nat (length (hs_W h1)) <= APARTIAL /\
(lp_grow (hs_expected h1) = true -> lp_vbytes (hs_expected h1) < MMAX) /\
blocks_bytes S1 + tr_peak (lp_tr (hs_expected h1) (Z.of_nat (length (hs_W h1)))) <= LIVE_MAX /\
mo_ok MT S1 (lp_cost MT (hs_expected h1) (Z.of_nat (length (hs_W h1)))) /\
(forall a, inFP (lp_FP (hs_expected h1)) a ->
  (inFP (dFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a) /\
rp_RM RP S1 (Z.to_nat (lp_cost MT_rk (hs_expected h1) (Z.of_nat (length (hs_W h1)))) +
  df_kr2 (hs_expected h1) (Z.of_nat (length (hs_W h1))) tl kr) /\
cnt_ok_pk RP (lp_peak (hs_expected h1) (Z.of_nat (length (hs_W h1)))) (ablocks B ly1 S1).
Proof.
eapply (df_push_pre_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* a callee's journal at G1 inside drain's G_DR: the bytes it keeps *)
Lemma df_keep_hi_x : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
(forall a, inG G1 a -> inG (G_DR B RG) a) ->
AJGX G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
eapply (df_keep_hi_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* the generic journal's image clause keeps an image byte only off PST *)
Lemma df_keep_img_x : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
~ YI16.sink_open_fp FP1 ->
AJGX G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ Exists (in_zr a) PST -> ~ inG G1 a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
eapply (df_keep_img_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_keep_blk_x : forall G1 STK1 sp1 FP1 lyc Sc Hpc (W : world SEGS) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 p n,
(forall a, inG G1 a -> inG (G_DR B RG) a) ->
ARx lyc Sc Hpc W memc mdc ->
AJGX G1 0 [] STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
In (p, n) (ablocks B lyc Sc) -> (forall i, 0 <= i < req_size n -> ~ inFP FP1 (p + i)) ->
In (p, n) (ablocks B ly2 S2) /\
(forall i, 0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) memc (p + i)).
Proof.
eapply (df_keep_blk_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_gx_pres_x : forall G0 STK sp0 FP ly S Hp (W0 : world SEGS) mem md own ly' S' Hp' (W' : world SEGS) mem' md' k,
AJGX G0 0 [] STK sp0 FP ly S Hp W0 mem md own ly' S' Hp' W' mem' md' k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
eapply (df_gx_pres_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_lp_call_x : forall cx Hp kr ly1 S1 Hp1 k1 W mc mdc regsc raw (l : hlist) (x : list byte) q qn kr2 Q,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
AJGX (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly1 S1 Hp1 W mc mdc k1 ->
spZ regsc = dsp0 cx - DRAIN_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> s0Z regsc < alloc_ceiling ->
getr regsc 10 = w64 (dHA RG cx + 64) -> getr regsc 11 = w64 q -> getr regsc 12 = w64 (Z.of_nat (length x)) ->
alist_at B ly1 S1 W mc (dHA RG cx + 64) l true ->
In (q, qn) (ablocks B ly1 S1) -> q <> hl_v l -> q + Z.of_nat (length x) <= q + req_size qn ->
garr8 SEGS (mrestrict (w_H W) mc) q (bzs x) ->
~ In (Z_to_bv 8 0) x -> Z.of_nat (length x) <= APARTIAL ->
(lp_grow l = true -> lp_vbytes l < MMAX) ->
blocks_bytes S1 + tr_peak (lp_tr l (Z.of_nat (length x))) <= LIVE_MAX ->
mo_ok MT S1 (lp_cost MT l (Z.of_nat (length x))) ->
(forall a, inFP (lp_FP l) a ->
  (inFP (dFP cx) a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a) ->
rp_RM RP S1 (Z.to_nat (lp_cost MT_rk l (Z.of_nat (length x))) + kr2) ->
cnt_ok_pk RP (lp_peak l (Z.of_nat (length x))) (ablocks B ly1 S1) ->
(forall W2 ly2 S2 Hp2 kk regs2 m2 md2 (l2 : hlist) d,
  AJGX (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
    (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 kk ->
  aregs_preserved regsc regs2 ->
  (forall p n i, In (p, n) (ablocks B ly1 S1) -> p <> hl_v l -> 0 <= i < req_size n ->
     abyte_kept W mc W2 m2 (p + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> ~ (dHA RG cx + 64 <= a < dHA RG cx + 80) -> abyte_kept W mc W2 m2 a) ->
  (forall a, as_errno B <= a < as_errno B + 4 -> abyte_kept W mc W2 m2 a) ->
  (forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W mc W2 m2 a) ->
  rom_view SEGS W2 m2 -> apres_kept B W mc W2 m2 -> frames S2 = frames S1 ->
  alist_at B ly2 S2 W2 m2 (dHA RG cx + 64) l2 true ->
  hl_recs l2 = hl_recs l ++ [(d, x)] ->
  hl_cap l2 = ListRep.grow_cap (hl_n l) (hl_cap l) ->
  (lp_grow l = false -> hl_v l2 = hl_v l) ->
  (forall rest,
   Permutation (ablocks B ly1 S1)
     ((if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []) ++ rest) ->
   Permutation (ablocks B ly2 S2)
     ((d, Z.of_nat (length x) + 1) :: (if lp_grow l then [(hl_v l2, AREC * hl_cap l2)] else []) ++ rest)) ->
  mo_le MT S1 S2 (lp_cost MT l (Z.of_nat (length x))) ->
  rp_RM RP S2 kr2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 raw m2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_list_push)) mc (seg_rom SEGS)) mdc) Q.
Proof.
eapply (df_lp_call_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* the frame lies at or above the allocator's ceiling (the journal's stack facts, as df_entry_full_x reads them) *)
Lemma df_cutjh_sp_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 regs,
(df_regs RG) cx s1 p0 k regs -> df_cutjh_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 ->
alloc_ceiling <= spZ regs <= 2 ^ 47.
Proof.
eapply (df_cutjh_sp_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

Lemma df_body_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W regs m md e1 h1 b Q,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> (df_regs RG) cx s1 p0 k regs -> Z.of_nat k < dnum s1 ->
df_cutjh_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> nth_error (ddata s1) k = Some b ->
(forall W2 c2, DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S k) W2 c2 -> SRr SEGS W2 c2 Q) ->
(forall W2 c2, DE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W2 c2 -> SRr SEGS W2 c2 Q) ->
SRr SEGS W (cfg_at SEGS (BASE + A_dr_feed) regs m md) Q.
Proof.
eapply (df_body_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* the round's k-th byte exists while k < dnum s1: the head text holds the n bytes from the offset *)
Lemma df_ddata_nth_x : forall cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1,
df_cutjh_x cx Hp kr s1 D k p0 ly1 S1 Hp1 k1 W m md e1 h1 -> Z.of_nat k < dnum s1 ->
exists b, nth_error (ddata s1) k = Some b.
Proof.
eapply (df_ddata_nth_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* The body for a byte that the round really has.  This is the walk. *)
Lemma df_feed_step_x : forall cx Hp kr s1 D k W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D k W1 c1 ->
Z.of_nat k < dnum s1 ->
(forall W2 c2, DRB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S k) W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
(forall W2 c2, DE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).
Proof.
eapply (df_feed_step_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* W_drain_cx_x.v dr_feed_stmt_x *)
Theorem dr_feed_p_x : dr_feed_stmt_x B PST ARx MT RP MMAX RG.
Proof.
eapply (dr_feed_p_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

(* ---- FEEDS: the byte loop, by induction on the bytes left (W_drain_cx_x.v dr_feeds_stmt_x). ---- *)
Theorem dr_feeds_p_x : dr_feeds_stmt_x B PST ARx MT RP MMAX RG.
Proof.
eapply (dr_feeds_p_xR (@wle SEGS)); first [exact (fun W => @wle_refl SEGS W) | exact (fun W1 W2 W3 => @wle_trans SEGS W1 W2 W3) | exact (fun W W' H => H) | eassumption].
Qed.

End cx.
End bx.
End ax.
