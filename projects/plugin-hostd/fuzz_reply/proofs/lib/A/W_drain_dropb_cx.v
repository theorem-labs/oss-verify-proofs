(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the INTERFACE between the two halves of the DROP segment of the
   ASan walk of fuzz_reply's drain (W_drain_cx.v dr_drop_stmt, 0x835ac .. 0x836bc / 0x83a4c).
   Nothing about the walk is proved here: the file fixes the cut DDM at 0x83668 - the join of the two
   arms of the `pending_off == v[0].n` test at 0x83600, i.e. after the inlined list_drop and before
   `n < 0` / `n == 0` / `s->used += n` / memchr #1 - and the statement dr_dropb_stmt of the second
   half, so the two halves are proved in parallel:
     W_drain_drop.v   dr_drop_of : dr_dropb_stmt -> dr_drop_stmt B MT MMAX RG
                      (DE -> DDM: pending_off += n, free #1 0x83618, __asan_memmove 0x83648,
                       h->pending.n -= 1, h->pending_off = 0)
     W_drain_dropb.v  dr_dropb : dr_dropb_stmt
                      (DDM -> DLL 0 q / DLR 0: the n < 0 and n == 0 arms refuted, s->used += n at
                       0x83684, memchr #1 at 0x836a4, and the line loop's first cut)
   The pure model lemmas dm_* that both halves need are proved here, so neither half copies them.
   The Section header below is W_drain_cx.v's, verbatim. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_dropb_cx.v, with its module paths changed; 81 of its 383 lines of code are new or changed and 14 lines of the source are left out. *)
(* The INTERFACE between the two halves of the DROP segment of the ASan walk of fuzz_reply's drain
   Nothing about the walk is proved here: the file fixes the cut DDM at 0x83668 - the join of the two
   arms of the `pending_off == v[0].n` test at 0x83600, i.e. after the inlined list_drop and before
   `n < 0` / `n == 0` / `s->used += n` / memchr #1 - and the statement dr_dropb_stmt of the second
   half, so the two halves are proved in parallel:
     W_drain_drop.v   dr_drop_of : dr_dropb_stmt -> dr_drop_stmt B MT MMAX RG
                      (DE -> DDM: pending_off += n, free #1 0x83618, __asan_memmove 0x83648,
                       h->pending.n -= 1, h->pending_off = 0)
     W_drain_dropb.v  dr_dropb : dr_dropb_stmt
                      (DDM -> DLL 0 q / DLR 0: the n < 0 and n == 0 arms refuted, s->used += n at
                       0x83684, memchr #1 at 0x836a4, and the line loop's first cut)
   The pure model lemmas dm_* that both halves need are proved here, so neither half copies them.
   The Section header below is W_drain_cx.v's, verbatim. *)
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
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx.
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
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
(* errno's 4 bytes are writable image bytes in the segments' own view (a .bss cell of the RW LOAD), so aout_at's
   errno cell stays writable across an allocator call whatever the call leaves present (the allocator rules keep
   errno's view but exclude it from presence; found by DropWhole at free #1).  Decided at the pinned placement. *)
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
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
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- The line loop before its first line (plain drain_b.v:5551 rtk_p0). ---- *)
Lemma dm_drlp0 : forall s, drlp s 0 = [].
Proof. intros s. reflexivity. Qed.

Lemma dm_dskp0 : forall s, dskp s 0 = drain_b_c.ds_skip s.
Proof. intros s. reflexivity. Qed.

Lemma dm_dlno0 : forall s, dlno s 0 = drain_b_c.ds_no s.
Proof. intros s. exact (Z.add_0_r (drain_b_c.ds_no s)). Qed.

Lemma dm_dloc0 : forall cx s, dloc cx s 0 = drain_b_c.ds_ocap s.
Proof. intros cx s. reflexivity. Qed.

Lemma dm_dlH0 : forall cx s, dlH cx s 0 = drain_b_c.ds_H s.
Proof. intros cx s. reflexivity. Qed.

Lemma dm_dlka0 : forall cx s, dlka cx s 0 = drain_b_c.ds_ka s.
Proof. intros cx s. reflexivity. Qed.

Lemma dm_dbound0 : forall s, dbound s 0.
Proof. intros s. unfold dbound. split; [lia | left; reflexivity]. Qed.

(* ---- The line loop's lines from the chunk the round added (plain drain_b.v:2797-2955 / W_drain_gs.v:74). ---- *)
Lemma dm_scan_nz_app : forall u sk acc d, nozero u -> scan sk acc (u ++ d) = scan sk (acc ++ u) d.
Proof.
  induction u as [|b u IH]; intros sk acc d Hz.
  - rewrite app_nil_r. reflexivity.
  - pose proof (Forall_inv Hz) as Hb. pose proof (Forall_inv_tail Hz) as Hu. cbn [app].
    rewrite (scan_nz sk acc b (u ++ d) Hb), (IH sk (acc ++ [b]) d Hu), <- app_assoc. reflexivity.
Qed.

Lemma dm_drlq0 : forall s, nozero (drain_b_c.ds_u s) -> drlq s 0 = drl s.
Proof.
  intros s Hz. unfold drlq, drl, dchunk, chunk, dW. rewrite dm_dskp0, skipn_O.
  rewrite (dm_scan_nz_app (drain_b_c.ds_u s) (drain_b_c.ds_skip s) [] (ddata s) Hz). cbn [app].
  destruct (scan (drain_b_c.ds_skip s) (drain_b_c.ds_u s) (ddata s)) as [[sk r] ls].
  destruct (Nat.ltb LINE_LIMIT (length r)); reflexivity.
Qed.

(* ---- The pending bytes split at the round's n (plain drain_b.v:5534 rtk_ps, 6729 rtd_ps). ---- *)
Lemma dm_ps : forall s, dwf s -> 0 <= dnum s ->
  pstream s = ddata s ++ prest (drain_b_c.ds_pend s) (drain_b_c.ds_off s + dnum s).
Proof.
  intros s (W0 & _) N0. unfold pstream, ddata, dhead.
  destruct (drain_b_c.ds_pend s) as [|r rs]; cbn [prest].
  - rewrite skipn_nil, firstn_nil. reflexivity.
  - rewrite app_assoc. f_equal.
    rewrite <- (firstn_skipn (Z.to_nat (dnum s)) (skipn (Z.to_nat (drain_b_c.ds_off s)) r)) at 1. f_equal.
    rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma dm_ps_whole : forall s, dwhole s = true ->
  prest (dtail s) 0 = prest (drain_b_c.ds_pend s) (drain_b_c.ds_off s + dnum s).
Proof.
  intros s W. unfold dwhole, dhead in W. apply Z.eqb_eq in W. unfold dtail.
  revert W. destruct (drain_b_c.ds_pend s) as [|r rs]; intros W; cbn [prest] in W |- *; [reflexivity|].
  rewrite W, Nat2Z.id, skipn_all. destruct rs as [|r1 rs]; reflexivity.
Qed.

Lemma dm_ps_next : forall cx s,
  pstream (dnext (dlive cx) (dxmx cx) s) = prest (drain_b_c.ds_pend s) (drain_b_c.ds_off s + dnum s).
Proof.
  intros cx s. unfold pstream, dnext. cbn [drain_b_c.ds_pend drain_b_c.ds_off].
  destruct (dwhole s) eqn:W; [exact (dm_ps_whole s W) | reflexivity].
Qed.

Lemma dm_ps_split : forall cx s, dwf s -> 0 <= dnum s ->
  pstream s = ddata s ++ pstream (dnext (dlive cx) (dxmx cx) s).
Proof. intros cx s W N. rewrite dm_ps_next. exact (dm_ps s W N). Qed.

(* ---- The round's data length. ---- *)
Lemma dm_dnum_le : forall s, dnum s <= Z.of_nat (length (dhead s)) - drain_b_c.ds_off s.
Proof. intros s. unfold dnum. lia. Qed.

Lemma dm_ddata_len : forall s, dwf s -> 0 <= dnum s -> Z.of_nat (length (ddata s)) = dnum s.
Proof.
  intros s (W0 & W1) N0. pose proof (dm_dnum_le s) as D. unfold ddata. unfold dhead in D |- *.
  destruct (drain_b_c.ds_pend s) as [|r rs] eqn:E.
  - rewrite skipn_nil, firstn_nil. cbn [length] in D |- *. lia.
  - specialize (W1 r rs eq_refl). rewrite length_firstn, length_skipn. lia.
Qed.

Lemma dm_dW_len : forall s, dwf s -> 0 <= dnum s ->
  Z.of_nat (length (dW s)) = Z.of_nat (length (drain_b_c.ds_u s)) + dnum s.
Proof. intros s W N. unfold dW. rewrite length_app, Nat2Z.inj_add, (dm_ddata_len s W N). reflexivity. Qed.

(* ---- The lines a chunk and a feed can produce (plain drain_b.v:2835 scan_lines_le, 5543 rtk_chunk_le). ---- *)
Lemma dm_scan_zero_snd : forall sk acc d, snd (scan sk acc (0 :: d)) =
  if (sk || Nat.ltb LINE_LIMIT (length acc))%bool then snd (scan false [] d) else acc :: snd (scan false [] d).
Proof. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma dm_scan_lines_le : forall d sk acc, (length (snd (scan sk acc d)) <= length d)%nat.
Proof.
  induction d as [|b d IH]; intros sk acc; [cbn; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb].
  - rewrite dm_scan_zero_snd. pose proof (IH false []) as I.
    destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; cbn [length]; lia.
  - rewrite (scan_nz sk acc b d Hb). pose proof (IH sk (acc ++ [b])). cbn [length]. lia.
Qed.

Lemma dm_chunk_le : forall u sk d, (length (snd (chunk u sk d)) <= length d)%nat.
Proof.
  intros u sk d. unfold chunk. pose proof (dm_scan_lines_le d sk u) as X.
  destruct (scan sk u d) as [[sk' r] ls]. cbn [snd] in X. cbv beta iota zeta.
  destruct (Nat.ltb LINE_LIMIT (length r)); exact X.
Qed.

Lemma dm_lines_le : forall st d, (length (lines st d) <= length d)%nat.
Proof.
  intros st d. revert st. induction d as [|b d IH]; intros st; [cbn; lia|].
  rewrite lines_cons. pose proof (IH (fst (RelayModel.step st b))) as I.
  destruct (snd (RelayModel.step st b)); cbn [length]; lia.
Qed.

(* ---- The round state seen from the line loop (plain drain_b.v:5558 rtk_dv, 6721 rtd_dv). ---- *)
Lemma dm_dv_keep : forall cx s, dwhole s = false ->
  dvirt cx s (drain_b_c.ds_skip s) (drain_b_c.ds_H s) (drain_b_c.ds_ka s) (drain_b_c.ds_no s)
    (drain_b_c.ds_ocap s) =
  drain_b_c.DS (drain_b_c.ds_cap s) (dW s) (drain_b_c.ds_skip s) (drain_b_c.ds_H s) (drain_b_c.ds_ka s)
    false (drain_b_c.ds_pend s) (drain_b_c.ds_off s + dnum s) (feed (drain_b_c.ds_ref s) (ddata s))
    (drain_b_c.ds_en s + Z.of_nat (length (dref s)))
    (pcapm (drain_b_c.ds_en s) (drain_b_c.ds_ecap s) (dref s))
    (drain_b_c.ds_no s) (drain_b_c.ds_ocap s).
Proof. intros cx s W. unfold dvirt, dnext. rewrite W. reflexivity. Qed.

Lemma dm_dv_whole : forall cx s, dwhole s = true ->
  dvirt cx s (drain_b_c.ds_skip s) (drain_b_c.ds_H s) (drain_b_c.ds_ka s) (drain_b_c.ds_no s)
    (drain_b_c.ds_ocap s) =
  drain_b_c.DS (drain_b_c.ds_cap s) (dW s) (drain_b_c.ds_skip s) (drain_b_c.ds_H s) (drain_b_c.ds_ka s)
    false (dtail s) 0 (feed (drain_b_c.ds_ref s) (ddata s))
    (drain_b_c.ds_en s + Z.of_nat (length (dref s)))
    (pcapm (drain_b_c.ds_en s) (drain_b_c.ds_ecap s) (dref s))
    (drain_b_c.ds_no s) (drain_b_c.ds_ocap s).
Proof. intros cx s W. unfold dvirt, dnext. rewrite W. reflexivity. Qed.

Lemma dm_dwf_virt : forall cx s, dwf s -> dstrict s -> 0 < dnum s ->
  dwf (dvirt cx s (drain_b_c.ds_skip s) (drain_b_c.ds_H s) (drain_b_c.ds_ka s) (drain_b_c.ds_no s)
         (drain_b_c.ds_ocap s)).
Proof.
  intros cx s (W0 & W1) _ N. destruct (dwhole s) eqn:E.
  - rewrite (dm_dv_whole cx s E). unfold dwf. cbn [drain_b_c.ds_off drain_b_c.ds_pend].
    split; [lia|]. intros r rs _. lia.
  - rewrite (dm_dv_keep cx s E). unfold dwf. cbn [drain_b_c.ds_off drain_b_c.ds_pend].
    split; [lia|]. intros r rs P. pose proof (dm_dnum_le s) as D. unfold dhead in D. rewrite P in D. lia.
Qed.

(* ---- list_drop's request (W_drain_model.v ddrop). ---- *)
Lemma dm_ddrop_keep : forall s a, dwhole s = false -> ddrop s a = [].
Proof. intros s a W. unfold ddrop. rewrite W. reflexivity. Qed.

Lemma dm_ddrop_whole : forall s a, dwhole s = true ->
  ddrop s a = [RelayRunT.RFree (Z.of_nat (length (dhead s)) + 1) (nth 0 (drain_b_c.da_pend a) RelayRunF.adr0)].
Proof. intros s a W. unfold ddrop. rewrite W. reflexivity. Qed.

Lemma dm_nret_ddrop : forall s a, RelayRunT.nret YO0i.sptr (ddrop s a) = 0%nat.
Proof. intros s a. unfold ddrop. destruct (dwhole s); reflexivity. Qed.

Lemma dm_cost_ddrop : forall s a, tr_cost MT (ddrop s a) = (if dwhole s then mo_free MT else 0).
Proof.
  intros s a. unfold ddrop, tr_cost, ListTr.list_drop_tra. destruct (dwhole s); cbn [fold_right]; lia.
Qed.

Lemma dm_alloc_ddrop : forall s a, tr_alloc (ddrop s a) = 0.
Proof. intros s a. unfold ddrop, tr_alloc, ListTr.list_drop_tra. destruct (dwhole s); reflexivity. Qed.

Lemma dm_max_ddrop : forall s a, tr_max (ddrop s a) = 0.
Proof. intros s a. unfold ddrop, tr_max, ListTr.list_drop_tra. destruct (dwhole s); reflexivity. Qed.

(* ---- The meters over an append (W_drain_gs.v:738-761). ---- *)
Lemma dm_tr_cost_app : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)),
  tr_cost MT (t1 ++ t2) = tr_cost MT t1 + tr_cost MT t2.
Proof.
  intros t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
  cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

Lemma dm_tr_alloc_app : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)),
  tr_alloc (t1 ++ t2) = tr_alloc t1 + tr_alloc t2.
Proof.
  intros t1 t2. unfold tr_alloc. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
  cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

Lemma dm_tr_max_nonneg : forall (t : list (RelayRunT.rev YO0i.sptr)), 0 <= tr_max t.
Proof.
  intros t. unfold tr_max. induction t as [|ev t IH]; [cbn [fold_right]; lia|].
  cbn [fold_right]. destruct ev; lia.
Qed.

Lemma dm_tr_max_app : forall (t1 t2 : list (RelayRunT.rev YO0i.sptr)),
  tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof.
  intros t1 t2. pose proof (dm_tr_max_nonneg t2) as H2. unfold tr_max in *.
  induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
  cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.
(* ================================================================================================
   The cut DDM (0x83668).  Both arms of the 0x83600 test reach it with the same registers:
   s6 = s (SA), s7 = &g_s[j], s8 = shadow(SA), s9 = SA + 32, s10 = SA + 16, s11 = SA + 24,
   s3 = n, s2 / s1 / s0 / s5 the globals' kept registers.  The harness side of the round is DONE
   (the offset advanced, or the head text freed and the record array moved down); the relay entry
   is still the round's - s->used is updated after the join, by the second half.
   ================================================================================================ *)
Definition A_dr_join : Z := AF_fr_drain + 0x58c.      (* 0x83668 *)

(* the round state the line loop sees, at p = 0 (W_drain_cx.v dvirt) *)
Definition dsv (cx : dcx) (s1 : drain_b_c.dstate) : drain_b_c.dstate :=
  dvirt cx s1 (drain_b_c.ds_skip s1) (drain_b_c.ds_H s1) (drain_b_c.ds_ka s1)
        (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1).

(* the relay entry after `s->used += n`: the n bytes handed over move from the junk into the buffer.
   The second half needs it; it is named here so both halves speak of the same entry. *)
Definition dr_used (e : rentry) (n : Z) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e + n) (re_cap e)
     (re_hp e) (re_kh e) (re_pad2 e) (re_keys e)
     (re_U e ++ firstn (Z.to_nat n) (re_junk e)) (skipn (Z.to_nat n) (re_junk e)).

Definition DDM (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_join) regs1 m1 md1 /\
(* ---- the registers the rest of the round reads ---- *)
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 23 = w64 (dHA RG cx) /\ getr regs1 19 = w64 (dnum s1) /\
getr regs1 22 = w64 (dxSA cx) /\ getr regs1 25 = w64 (dxSA cx + 32) /\
getr regs1 26 = w64 (dxSA cx + 16) /\ getr regs1 27 = w64 (dxSA cx + 24) /\
(* ---- the frame: the prologue's constants, and the four slots dregs_line asks of DLL / DLR ---- *)
dr_frame RG cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) /\
(* ---- the round's n, and the n bytes already in the relay's buffer after s->used ---- *)
0 < dnum s1 /\ dnum s1 <= 16384 /\
bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 /\
(* ---- the memory core, at the round state the line loop sees ---- *)
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 (dsv cx s1) out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DSAME cx e1 h1 /\
(* ---- the relay entry is still the round's: s->used is not yet updated ---- *)
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
(* ---- the harness source after fuzz_recv's tail (the offset, or the drop) ---- *)
hs_eintr h1 = 0 /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend (dnext (dlive cx) (dxmx cx) s1) /\
hs_off h1 = drain_b_c.ds_off (dnext (dlive cx) (dxmx cx) s1) /\
hs_state h1 = feed (drain_b_c.ds_ref s1) (ddata s1) /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) /\
hl_cap (hs_expected h1) = pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) /\
(* ---- the history, the round's start and what is still owed to the allocator.  DHIST's two byte
   lists are LCORE's at p = 0: the round's n bytes are already taken, so both are D ++ ddata s1
   (with D alone the first conjunct would contradict dm_ps_split, since 0 < dnum s1). ---- *)
DHIST cx (dsv cx s1) (D ++ ddata s1) (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1
  (Z.of_nat (length (drl s1))) /\
RSTART cx s1 D /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1)
  (drain_b_c.ds_H s1) (drain_b_c.ds_ka s1) (drl s1) jb o ha ks tl /\
dbud MT MMAX cx S1 spent tl.

(* DROPB: DDM 0x83668 -> `n < 0` (0x83668) and `n == 0` (0x8366c) refuted by `0 < dnum s1`,
   s->used += n (0x83684) and memchr(s->buf, 0, s->used) (0x836a4) -> the first line of the buffer
   (DLL with p = 0) or no line at all (DLR with p = 0, through 0x83a48 mv s10,s8).
   `drlq s1 0 = drl s1` is dm_drlq0 above, from `~ In 0 (re_U e1)` and `bzs (re_U e1) = ds_u s1`;
   the entry DLL / DLR carry is `dr_used e1 (dnum s1)`. *)
Definition dr_dropb_stmt : Prop :=
forall cx s1 D W1 c1,
DBASE B MT MMAX RG cx -> DDM cx s1 D W1 c1 ->
(forall q W2 c2, DLL B MT MMAX RG cx s1 D 0 q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, DLR B MT MMAX RG cx s1 D 0 W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this interface (DR_x slice B, 2026-10-30): the cut DDM over W_drain_cx_x.v's Section
   variables (B PST ARx MT RP MMAX RG), with the entry's ghost list Hp and budget kr after cx and the cut's own ghost
   list Hp1 an existential right after S1, as W_drain_cx_x.v threads them, and the second half's statement over it.
   Everything above this line is unchanged; the twin only adds names (the AR name with _x).
   - DDM_x is DDM with W_drain_cx_x.v's DMEM_x for DMEM and dbud_x for dbud (the room at the cut's state with MT_rk's
     count of the requests still owed, tl, on top of kr, and the counts at dr_pk's shape over tl).
   - dr_dropb_stmt_x is dr_dropb_stmt over DBASE_x, DDM_x, DLL_x, DLR_x and dPOST_x, in the shape of W_drain_cx_x.v's
     dr_drop_stmt_x.
   - The AR-free names above (A_dr_join, dsv, dr_used, the model lemmas dm_* ) are CITED. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_cx W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.

(* The carriers of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, and every carrier or spec it names -> its R twin;
   every other token is the strict text's. The strict <name> is <name>R at R := wle. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Definition DDM_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS)
(c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_join) regs1 m1 md1 /\
(* ---- the registers the rest of the round reads ---- *)
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 18 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 8 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 21 = w64 SHADOW_OFF /\
getr regs1 23 = w64 (dHA RG cx) /\ getr regs1 19 = w64 (dnum s1) /\
getr regs1 22 = w64 (dxSA cx) /\ getr regs1 25 = w64 (dxSA cx + 32) /\
getr regs1 26 = w64 (dxSA cx + 16) /\ getr regs1 27 = w64 (dxSA cx + 24) /\
(* ---- the frame: the prologue's constants, and the four slots dregs_line asks of DLL / DLR ---- *)
dr_frame RG cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 56) 8 (dxSA cx) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 64) 8 (dxSA cx + 32) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 48) 8 (dxSA cx + 24) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 200) 8 (dxSA cx + 16) /\
(* ---- the round's n, and the n bytes already in the relay's buffer after s->used ---- *)
0 < dnum s1 /\ dnum s1 <= 16384 /\
bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 /\
(* ---- the memory core, at the round state the line loop sees ---- *)
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 (dsv cx s1) out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DSAME cx e1 h1 /\
(* ---- the relay entry is still the round's: s->used is not yet updated ---- *)
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
(* ---- the harness source after fuzz_recv's tail (the offset, or the drop) ---- *)
hs_eintr h1 = 0 /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend (dnext (dlive cx) (dxmx cx) s1) /\
hs_off h1 = drain_b_c.ds_off (dnext (dlive cx) (dxmx cx) s1) /\
hs_state h1 = feed (drain_b_c.ds_ref s1) (ddata s1) /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) /\
hl_cap (hs_expected h1) = pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) /\
(* ---- the history, the round's start and what is still owed to the allocator (DDM's text) ---- *)
DHIST cx (dsv cx s1) (D ++ ddata s1) (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1
  (Z.of_nat (length (drl s1))) /\
RSTART cx s1 D /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1)
  (drain_b_c.ds_H s1) (drain_b_c.ds_ka s1) (drl s1) jb o ha ks tl /\
dbud_x B MT RP MMAX cx kr ly1 S1 spent tl.

Definition dr_dropb_stmt_xR : Prop :=
forall cx Hp kr s1 D W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DDM_xR cx Hp kr s1 D W1 c1 ->
(forall q W2 c2, DLL_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D 0 q W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, DLR_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D 0 W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
End wR.


(* DDM (above) over ARx: the cut's ghost list Hp1 after S1, DMEM_x at the entry's Hp, dbud_x at the entry's kr *)
Definition DDM_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS)
(c1 : config) : Prop :=
DDM_xR (@wle SEGS) cx Hp kr s1 D W1 c1.

(* dr_dropb_stmt (above) over ARx, in the shape of W_drain_cx_x.v's dr_drop_stmt_x *)
Definition dr_dropb_stmt_x : Prop :=
dr_dropb_stmt_xR (@wle SEGS).

End cx.
End bx.
End ax.
