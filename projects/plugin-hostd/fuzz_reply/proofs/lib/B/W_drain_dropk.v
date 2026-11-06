(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B/W_drain_dropk.v, the model and memory bookkeeping of the image-B
   (fuzz_reply.asan-ubsan) drain stage DROP (lib/B/W_drain_drop.v, DE 0x838a0 -> DJ 0x8395c).  Proves no function
   (kind: segment lemma).  Over lib/B/W_drain_cx.v's cut predicates (not edited).
   What DROP does to the state (fuzz_reply.c:269-275 and relay.c's s->used += n):
     h->pending_off += n; if it reached the head text's length, list_drop (&h->pending, 0) and pending_off = 0;
     s->used += n (the n bytes are already in the relay's buffer, after the used ones).
   dd_arm_close rebuilds DMEM for the new entry dd_eadd e1 n and source dd_hset h1 l2 off2 from "every byte DMEM reads
   (ddK: a live block's, an image byte off the allocator's statics, drain's frame) outside ddX is kept" (ddX:
   g_s[j]'s pending head and pending_off, s->used, the pending list's blocks, the callee's scratch below drain's
   frame); dd_DJ assembles lib/B/W_drain_join.v's cut DJ at p = 0 from it and DE's model.
   Lemmas taken from lib/B/W_drain_feed.v (the FEED stage, on the base; imported, not copied): df_dmem_rebuild's
   proof shape, df_aentry_okx_kept, df_pu_alist_kept, df_pu_aentry_kept, df_lp_rq_out, df_pu_nd, df_nd_fst,
   df_blk_wr, df_pu_gs, df_wr_img. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx W_drain_dnrk W_drain_join
  W_drain_rest W_drain_feed.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
(* route R: SRrG (Reusable YA0nH) and the R specs (W_contract_xR.v), for the Section wR twins *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).


(* ------------------------------------------------------------------ the new source and entry *)
Definition dd_hset (h : hsrc) (l : hlist) (off : Z) : hsrc :=
HS (hs_fd h) (hs_open h) (hs_closed h) (hs_eintr h) l off (hs_partial h) (hs_pjunk h) (hs_npartial h)
  (hs_overlong h) (hs_pad h) (hs_expected h) (hs_held h).
Definition dd_eadd (e : rentry) (n : Z) : rentry :=
drr_eset e (re_skip e) (re_used e + n) (re_U e ++ firstn (Z.to_nat n) (re_junk e)) (skipn (Z.to_nat n) (re_junk e)).
Definition dd_recblk (r : Z * list byte) : Z * Z := (fst r, Z.of_nat (length (snd r)) + 1).

(* ------------------------------------------------------------------ the model *)
Lemma dd_scan_len : forall l sk acc, (length (snd (scan sk acc l)) <= length l)%nat.
Proof.
induction l as [|b l IH]; intros sk acc; [cbn; lia|].
cbn [scan]. destruct (Z.eqb b 0).
- specialize (IH false []). destruct (scan false [] l) as [[sk1 r1] ls1]. cbn [snd] in IH |- *.
  destruct (sk || Nat.ltb LINE_LIMIT (length acc)); cbn [length]; lia.
- specialize (IH sk (acc ++ [b])). cbn [length]. lia.
Qed.

Lemma dd_lines_len : forall l st, (length (lines st l) <= length l)%nat.
Proof.
unfold lines. induction l as [|b l IH]; intros st; [cbn; lia|].
cbn [feed_lines]. destruct (step st b) as [st1 o]. specialize (IH st1).
destruct (feed_lines st1 l) as [st2 ls]. cbn [snd] in IH |- *. destruct o; cbn [length]; lia.
Qed.

(* the pending bytes: the round's data, then what dnext leaves pending *)
Lemma dd_pstream : forall s, 0 <= drain_b_c.ds_off s -> 0 <= dnum s ->
drain_b_c.ds_off s + dnum s <= Z.of_nat (length (dhead s)) ->
pstream s = ddata s ++ prest (if dwhole s then dtail s else drain_b_c.ds_pend s)
                             (if dwhole s then 0 else drain_b_c.ds_off s + dnum s).
Proof.
intros s H0 Hn Hle. unfold pstream, ddata, dwhole, dtail. unfold dhead in *.
destruct (drain_b_c.ds_pend s) as [|r rs] eqn:E; cbn [length] in Hle.
- rewrite skipn_nil, firstn_nil. destruct (drain_b_c.ds_off s + dnum s =? Z.of_nat (length [])); reflexivity.
- cbn [prest]. destruct (Z.eqb_spec (drain_b_c.ds_off s + dnum s) (Z.of_nat (length r))) as [Ew | Ew].
  + rewrite firstn_all2 by (rewrite length_skipn; lia).
    destruct rs as [|r1 rs1]; cbn [prest concat]; [reflexivity|]. rewrite skipn_O. reflexivity.
  + cbn [prest]. rewrite app_assoc. f_equal.
    rewrite <- (firstn_skipn (Z.to_nat (dnum s)) (skipn (Z.to_nat (drain_b_c.ds_off s)) r)) at 1. f_equal.
    rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma dd_dwf_next : forall s, 0 <= drain_b_c.ds_off s -> 0 <= dnum s ->
drain_b_c.ds_off s + dnum s <= Z.of_nat (length (dhead s)) ->
0 <= (if dwhole s then 0 else drain_b_c.ds_off s + dnum s) /\
(forall r rs, (if dwhole s then dtail s else drain_b_c.ds_pend s) = r :: rs ->
  (if dwhole s then 0 else drain_b_c.ds_off s + dnum s) <= Z.of_nat (length r)).
Proof.
intros s H0 Hn Hle. destruct (dwhole s); [split; [lia | intros; lia]|].
split; [lia|]. intros r rs E. unfold dhead in Hle. rewrite E in Hle. exact Hle.
Qed.

(* p = 0: no line before p, the virtual state's no / oc / H / ka are the round's *)
Lemma dd_drlp0 : forall s, drlp s 0 = [].
Proof. reflexivity. Qed.
Lemma dd_dlno0 : forall s, dlno s 0 = drain_b_c.ds_no s.
Proof. intros s. unfold dlno. rewrite dd_drlp0. cbn. lia. Qed.

Lemma dd_drlq0 : forall s, nozero (drain_b_c.ds_u s) -> drlq s 0 = drl s.
Proof.
intros s Hu. unfold drlq, drl, dchunk, chunk, dskp, dW.
change (Nat.eqb 0 0) with true. cbv iota. change (skipn 0 (drain_b_c.ds_u s ++ ddata s)) with (drain_b_c.ds_u s ++ ddata s).
rewrite (dr_scan_app (drain_b_c.ds_u s) (ddata s) (drain_b_c.ds_skip s) []).
rewrite (dr_scan_nz _ _ [] Hu). cbn [app].
destruct (scan (drain_b_c.ds_skip s) (drain_b_c.ds_u s) (ddata s)) as [[sk r] ls].
destruct (Nat.ltb LINE_LIMIT (length r)); reflexivity.
Qed.

(* the round's lines from the virtual state, and the bytes they take *)
Lemma dd_drl_len : forall s, nozero (drain_b_c.ds_u s) -> (length (drl s) <= length (ddata s))%nat.
Proof.
intros s Hu. rewrite <- (dd_drlq0 s Hu). unfold drlq, dW, dskp.
change (Nat.eqb 0 0) with true. cbv iota. change (skipn 0 (drain_b_c.ds_u s ++ ddata s)) with (drain_b_c.ds_u s ++ ddata s).
rewrite (dr_scan_app (drain_b_c.ds_u s) (ddata s) (drain_b_c.ds_skip s) []).
rewrite (dr_scan_nz _ _ [] Hu). cbn [app].
pose proof (dd_scan_len (ddata s) (drain_b_c.ds_skip s) (drain_b_c.ds_u s)) as L.
destruct (scan (drain_b_c.ds_skip s) (drain_b_c.ds_u s) (ddata s)) as [[sk r] ls]. exact L.
Qed.

Lemma dd_eadd_okx_pure : forall e n, 0 <= n -> n <= Z.of_nat (length (re_junk e)) ->
re_U (dd_eadd e n) ++ re_junk (dd_eadd e n) = re_U e ++ re_junk e /\
Z.of_nat (length (re_U (dd_eadd e n))) = Z.of_nat (length (re_U e)) + n /\
Z.of_nat (length (re_junk (dd_eadd e n))) = Z.of_nat (length (re_junk e)) - n.
Proof.
intros e n H0 Hn. unfold dd_eadd, drr_eset. cbn [re_U re_junk].
split; [rewrite <- app_assoc, firstn_skipn; reflexivity|].
rewrite length_app, length_firstn, length_skipn. split; lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
#[local] Notation le8 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
#[local] Notation le4 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4.

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

Lemma dd_nodup_mid : forall (T : Type) (a b c : list T), List.NoDup (a ++ b ++ c) -> List.NoDup (a ++ c).
Proof.
intros T a b. induction b as [|x b IH]; intros c H; [exact H|].
apply IH. cbn [app] in H. apply List.NoDup_remove_1 in H. exact H.
Qed.

Lemma dd_nd_fst2 : forall (A C : list (Z * Z)) x, List.NoDup (map fst (A ++ C)) -> In x A -> ~ In (fst x) (map fst C).
Proof.
induction A as [|y A IH]; intros C x H Hx; [destruct Hx|].
cbn [app map] in H. inversion H as [|z l Hz Hl]; subst.
destruct Hx as [<- | Hx].
- intros Hc. apply Hz. rewrite map_app. apply in_or_app. right. exact Hc.
- exact (IH C x Hl Hx).
Qed.

Lemma dd_perm_mv : forall (T : Type) (A p Q : list T), Permutation (A ++ p ++ Q) (p ++ A ++ Q).
Proof. intros T A p Q. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. Qed.

(* the new entry is an entry *)
Lemma dd_aentry_add : forall ly S W m e n, aentry_okx B ly S W m e -> 0 < re_cap e ->
0 <= n -> n <= Z.of_nat (length (re_junk e)) -> aentry_okx B ly S W m (dd_eadd e n).
Proof.
intros ly S W m e n HE Hc Hn0 Hn.
destruct (dd_eadd_okx_pure e n Hn0 Hn) as (EUJ & EU & EJ).
destruct HE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
destruct H9 as [(Hc0 & _) | (_ & Hin & Hj & Hg)]; [lia|].
unfold aentry_okx. rewrite EU, EJ, EUJ.
unfold dd_eadd, drr_eset. cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split; [lia|]. split; [lia|].
split; [right; split; [exact Hc|]; split; [exact Hin|]; split; [lia | exact Hg]|].
split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13 | exact H14].
Qed.

(* the entry's 56 bytes with s->used rewritten, across a change of world *)
Lemma dd_entry_set : forall (W W' : world SEGS) m m' SA e u,
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) -> length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
(forall y, SA <= y < SA + 56 -> ~ (SA + 24 <= y < SA + 32) -> aview SEGS (w_H W') m' y = aview SEGS (w_H W) m y) ->
val_mem SEGS (arm W' m') (SA + 24) 8 u -> 0 <= u < 2 ^ 64 ->
forall U J, garr8 SEGS (arm W' m') SA (bzs (entry_bytes (drr_eset e (re_skip e) u U J))).
Proof.
intros W W' m m' SA e u Hg Hp1 Hp2 KM Vu Hu U J.
destruct (dnk_entry_fields _ _ _ Hg Hp1) as (G1 & G2 & G3 & G4 & G5 & G6).
assert (L4 : forall w, Z.of_nat (length (bzs (le4 w))) = 4)
  by (intros w; unfold bzs; rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4;
      reflexivity).
assert (L8 : forall w, Z.of_nat (length (bzs (le8 w))) = 8)
  by (intros w; unfold bzs; rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8;
      reflexivity).
assert (L44 : forall w v, Z.of_nat (length (bzs (le4 w ++ le4 v))) = 8)
  by (intros w v; unfold bzs; rewrite length_map, length_app,
      !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4; reflexivity).
assert (LP : Z.of_nat (length (bzs (re_pad1 e))) = 4) by (unfold bzs; rewrite length_map, Hp1; reflexivity).
assert (LT : Z.of_nat (length (bzs (le8 (Z_to_bv 64 (re_cap e)) ++ le8 (Z_to_bv 64 (re_hp e)) ++
  le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e))) = 24)
  by (unfold bzs; rewrite length_map, !length_app,
      !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8,
      !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4, Hp2; reflexivity).
assert (KEEP : forall a l, garr8 SEGS (arm W m) a l -> SA <= a -> a + Z.of_nat (length l) <= SA + 56 ->
  (a + Z.of_nat (length l) <= SA + 24 \/ SA + 32 <= a) -> garr8 SEGS (arm W' m') a l).
{ intros a l Hl H1 H2 H3. apply (garr8_frame SEGS _ _ a l Hl). intros x Hx.
  apply (mbyte_of_aview SEGS). apply KM; lia. }
rewrite dnk_entry_split. unfold drr_eset.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys].
change (re_nheld (RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) u (re_cap e) (re_hp e) (re_kh e)
  (re_pad2 e) (re_keys e) U J)) with (re_nheld e).
apply (proj2 (garr8_app SEGS _ _ _ _)). split; [apply KEEP; [exact G1 | lia | rewrite L44; lia | rewrite L44; lia]|].
rewrite L44.
apply (proj2 (garr8_app SEGS _ _ _ _)). split; [apply KEEP; [exact G2 | lia | rewrite L4; lia | rewrite L4; lia]|].
rewrite L4. replace (SA + 8 + 4) with (SA + 12) by lia.
apply (proj2 (garr8_app SEGS _ _ _ _)). split; [apply KEEP; [exact G3 | lia | rewrite LP; lia | rewrite LP; lia]|].
rewrite LP. replace (SA + 12 + 4) with (SA + 16) by lia.
apply (proj2 (garr8_app SEGS _ _ _ _)). split; [apply KEEP; [exact G4 | lia | rewrite L8; lia | rewrite L8; lia]|].
rewrite L8. replace (SA + 16 + 8) with (SA + 24) by lia.
apply (proj2 (garr8_app SEGS _ _ _ _)).
split; [rewrite (dnk_le8_bytes u ltac:(lia)); apply dnk_le_garr8; [exact Vu | cbn; lia]|].
rewrite L8. replace (SA + 24 + 8) with (SA + 32) by lia.
apply KEEP; [exact G6 | lia | rewrite LT; lia | rewrite LT; lia].
Qed.

(* the source after DROP's stores: the pending list and pending_off replaced, all else kept *)
Lemma dd_asrc_set : forall ly1 S1 (W1 : world SEGS) m1 md1 ly2 S2 (W2 : world SEGS) m2 HA h1 l2 off2 pre,
AR SEGS B ly1 S1 W1 m1 md1 ->
asrc_at B ly1 S1 W1 m1 HA h1 ->
(forall a, HA <= a < HA + ASRC -> ~ (HA + 16 <= a < HA + 40) -> abyte_kept W1 m1 W2 m2 a) ->
(forall p n a, In (p, n) ((hs_partial h1, APARTIAL) :: alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) ->
   p <= a < p + req_size n -> abyte_kept W1 m1 W2 m2 a) ->
(forall b, In b ((hs_partial h1, APARTIAL) :: alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) ->
   In b (ablocks B ly2 S2)) ->
awr W2 m2 HA ASRC ->
alist_at B ly2 S2 W2 m2 (HA + 16) l2 false ->
hl_v l2 = hl_v (hs_pending h1) -> hl_cap l2 = hl_cap (hs_pending h1) ->
hl_recs (hs_pending h1) = pre ++ hl_recs l2 ->
val_mem SEGS (arm W2 m2) (HA + 32) 8 off2 ->
((hl_recs l2 = [] /\ off2 = 0) \/ (exists r rs, hl_recs l2 = r :: rs /\ 0 <= off2 < Z.of_nat (length (snd r)))) ->
asrc_at B ly2 S2 W2 m2 HA (dd_hset h1 l2 off2).
Proof.
intros ly1 S1 W1 m1 md1 ly2 S2 W2 m2 HA h1 l2 off2 pre HAR HS KH KB HBL HAW HL2 Ev Ec Erecs Voff Hoff.
pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & H24).
assert (VH : forall a n v, HA <= a -> a + Z.of_nat n <= HA + ASRC -> (a + Z.of_nat n <= HA + 16 \/ HA + 40 <= a) ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W2 m2) a n v).
{ intros a n v Ha Hn Hd Hv. apply (akept_vm W1 m1); [|exact Hv]. intros x Hx. apply KH; lia. }
assert (LK : forall LA l lines, HA + 40 <= LA -> LA + 16 <= HA + ASRC ->
  (forall b, In b (alist_blks l) ->
     In b ((hs_partial h1, APARTIAL) :: alist_blks (hs_expected h1) ++ alist_blks (hs_held h1))) ->
  alist_at B ly1 S1 W1 m1 LA l lines -> alist_at B ly2 S2 W2 m2 LA l lines).
{ intros LA l lines HL1 HL2' Hsub HL. apply (alist_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 LA l lines HL).
  - apply (df_pu_alist_kept B RG ly1 S1 W1 W2 m1 m2 LA l lines HL).
    + intros a Ha. apply KH; unfold ASRC in *; lia.
    + intros p n a Hpn Ha. exact (KB p n a (Hsub _ Hpn) Ha).
  - intros b Hb. exact (HBL b (Hsub b Hb)). }
unfold asrc_at, dd_hset.
cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
  hs_expected hs_held].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H1]|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H2]|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H3]|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H4]|].
split; [exact HAW|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
split; [exact HL2|].
split; [exact Voff|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H12]|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H13]|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H14]|].
split; [exact Hoff|].
split; [exact H16|]. split; [exact H17|].
split; [apply HBL; left; reflexivity|].
split; [exact H19|].
split.
{ apply (akept_garr8 W1 m1); [|exact H20]. intros x Hx. apply (KB (hs_partial h1) APARTIAL x); [left; reflexivity|].
  unfold bzs in Hx. rewrite length_map, H19 in Hx.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia. }
split; [exact H21|].
split; [apply (LK (HA + 64) _ true); [lia | unfold ASRC; lia
  | intros b Hb; right; apply in_or_app; left; exact Hb | exact H22]|].
split; [apply (LK (HA + 80) _ true); [lia | unfold ASRC; lia
  | intros b Hb; right; apply in_or_app; right; exact Hb | exact H23]|].
apply (proj2 (stdpp.base.NoDup_ListNoDup _)). apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in H24.
unfold hs_blocks, list_blocks in H24 |- *.
cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
  hs_expected hs_held] in H24 |- *.
rewrite Ev, Ec. rewrite Erecs, map_app in H24. rewrite <- !app_assoc in H24.
pose proof (dd_nodup_mid _ _ (map fst pre) _ H24) as X. rewrite <- ?app_assoc in X. rewrite <- ?app_assoc. exact X.
Qed.

(* df_dmem_rebuild (lib/B/W_drain_feed.v:847) with the entry replaced as well *)
Lemma dd_dmem_close : forall cx ly S W m md k e h s out ev sent LB ly' S' W' m' md' k' e' h',
DMEM B RG cx ly S W m md k e h s out ev sent LB ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly' S' W' m' md' k' ->
rom_view SEGS W' m' -> apres_kept B W m W' m' -> frames S' = frames S ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
garr8 SEGS (arm W' m') (dxSA cx) (bzs (entry_bytes e')) -> awr W' m' (dxSA cx) AENT ->
aentry_okx B ly' S' W' m' e' ->
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= a < dHA RG cx + ASRC) ->
   abyte_kept W m W' m' a) ->
akept W m W' m' (aout_fp B RG (drain_b_c.ds_ocap s) out) ->
asrc_at B ly' S' W' m' (dHA RG cx) h' ->
Permutation (ablocks B ly' S')
  ((dxG cx, ATABLE) :: aentry_blks e' ++ asrc_blks h' ++ aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) ->
DMEM B RG cx ly' S' W' m' md' k' e' h' s out ev sent LB.
Proof.
intros cx ly S W m md k e h s out ev sent LB ly' S' W' m' md' k' e' h' HD HJ' KR KP KF KS Hent' Hawr' Hokx' KG KO HS' HP'.
destruct HD as (HJ & Hrom & Hpres & Hfr & HFR & Hent & Hawr & Hokx & Hsrc & Hoth & Hgsk & Hout & Hlive & Hperm).
assert (HIN : forall b, In b (aout_blks (drain_b_c.ds_ocap s) out) -> In b (ablocks B ly' S')).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HP'|]. right.
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (VK : forall a n v, dsp0 cx - DRAIN_FRAME <= a -> a + Z.of_nat n <= dsp0 cx ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W' m') a n v).
{ intros a n v H1 H2 Hv. apply (akept_vm W m); [intros x Hx; apply KS; lia | exact Hv]. }
split; [exact HJ'|].
split; [exact KR|].
split; [intros a H1 H2 H3 H4; exact (KP a H1 H2 H3 (Hpres a H1 H2 H3 H4))|].
split; [rewrite KF; exact Hfr|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 &
    F18 & F19 & F20 & F21 & F22 & F23 & FS).
  unfold DRAIN_FRAME in VK |- *.
  repeat split; try (apply VK; [simpl Z.of_nat; lia | simpl Z.of_nat; lia | assumption]).
  unfold dr_saved, DR_SAVE_OFF. intros i Hi. apply VK; [lia | simpl Z.of_nat; lia | exact (FS i Hi)]. }
split; [exact Hent'|].
split; [exact Hawr'|].
split; [exact Hokx'|].
split; [exact HS'|].
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Vo). exists f, o.
  assert (KI : forall x, rg_s RG + ASRC * Z.of_nat i <= x < rg_s RG + ASRC * Z.of_nat i + 8 ->
    abyte_kept W m W' m' x).
  { intros x Hx. apply KG; unfold dHA, ASRC in *; [lia|]. intros Hc. apply Hij. lia. }
  split; [|split; [|exact Vo]]; (apply (akept_vm W m); [intros x Hx; apply KI; simpl Z.of_nat in Hx; lia|]);
  assumption. }
split; [intros x Hx1 Hx2; exact (df_bk_trans _ _ _ _ _ _ x (Hgsk x Hx1 Hx2) (KG x Hx1 Hx2))|].
split; [exact (aout_at_kept B RG ly S W m ly' S' W' m' _ _ _ _ _ _ Hout KO HIN)|].
split; [exact Hlive | exact HP'].
Qed.


Lemma dd_perm_split : forall (t p : Z * Z) (AE AP AX AO : list (Z * Z)),
Permutation (t :: AE ++ (p :: AP ++ AX) ++ AO) (t :: (AE ++ (p :: AX) ++ AO) ++ AP).
Proof.
intros t p AE AP AX AO. apply perm_skip. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
apply perm_skip. rewrite <- !app_assoc.
eapply Permutation_trans; [apply (Permutation_app_comm AP (AX ++ AO))|]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma dd_perm_drop : forall (t p : Z * Z) (AE VP P R2 AX AO : list (Z * Z)),
Permutation (t :: (AE ++ (p :: AX) ++ AO) ++ (VP ++ P ++ R2)) (P ++ t :: AE ++ (p :: (VP ++ R2) ++ AX) ++ AO).
Proof.
intros t p AE VP P R2 AX AO.
transitivity (P ++ t :: (AE ++ (p :: AX) ++ AO) ++ (VP ++ R2)).
- replace (t :: (AE ++ (p :: AX) ++ AO) ++ VP ++ P ++ R2) with ((t :: (AE ++ (p :: AX) ++ AO) ++ VP) ++ P ++ R2)
    by (cbn [app]; rewrite <- !app_assoc; reflexivity).
  eapply Permutation_trans; [apply dd_perm_mv|]. cbn [app]. rewrite <- !app_assoc. reflexivity.
- apply Permutation_app_head. apply Permutation_sym. apply dd_perm_split.
Qed.

(* ------------------------------------------------------------------ DMEM after DROP *)
Definition ddX (cx : dcx) (lo : Z) (XB : Z -> Prop) (a : Z) : Prop :=
(dHA RG cx + 16 <= a < dHA RG cx + 40) \/ (dxSA cx + 24 <= a < dxSA cx + 32) \/ XB a \/
(lo <= a < dsp0 cx - DRAIN_FRAME).
(* the bytes DMEM reads: a live block's, an image byte off the allocator's statics, drain's frame.  The list_drop
   call frees a text, so the allocator's own bytes (statics, chunk headers) are not kept and are not asked for. *)
Definition ddK (ly : alayout) (S : astate) (cx : dcx) (a : Z) : Prop :=
(exists p q, In (p, q) (ablocks B ly S) /\ p <= a < p + req_size q) \/
(in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)) \/
(dsp0 cx - DRAIN_FRAME <= a < dsp0 cx).

Lemma dd_arm_close : forall cx ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 s out ev sent LB
  ly2 S2 (W2 : world SEGS) m2 md2 k2 lo XB l2 off2 pre n,
DBASE B MT MMAX RG cx ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 s out ev sent LB ->
ajournal_gx SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 W2 m2 md2 k2 ->
rom_view SEGS W2 m2 -> apres_kept B W1 m1 W2 m2 -> frames S2 = frames S1 ->
alloc_ceiling <= lo ->
(forall a, XB a -> exists p q, In (p, q) (alist_blks (hs_pending h1)) /\ p <= a < p + req_size q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ ddX cx lo XB a -> ddK ly1 S1 cx a -> abyte_kept W1 m1 W2 m2 a) ->
alist_at B ly2 S2 W2 m2 (dHA RG cx + 16) l2 false ->
hl_v l2 = hl_v (hs_pending h1) -> hl_cap l2 = hl_cap (hs_pending h1) ->
hl_recs (hs_pending h1) = pre ++ hl_recs l2 ->
Permutation (ablocks B ly1 S1)
  (map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) pre ++ ablocks B ly2 S2) ->
val_mem SEGS (arm W2 m2) (dHA RG cx + 32) 8 off2 ->
((hl_recs l2 = [] /\ off2 = 0) \/ (exists r rs, hl_recs l2 = r :: rs /\ 0 <= off2 < Z.of_nat (length (snd r)))) ->
val_mem SEGS (arm W2 m2) (dxSA cx + 24) 8 (re_used e1 + n) ->
0 <= n -> n <= Z.of_nat (length (re_junk e1)) -> 0 < re_cap e1 ->
DMEM B RG cx ly2 S2 W2 m2 md2 k2 (dd_eadd e1 n) (dd_hset h1 l2 off2) s out ev sent LB.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 e1 h1 s out ev sent LB ly2 S2 W2 m2 md2 k2 lo XB l2 off2 pre n
  HB HM HJ2 Hrv2 HPK2 HFR2 Hlo HXB KX HL2 Ev Ec Erecs HPm Voff Hoff Vu Hn0 Hnj Hcp.
pose proof HM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
pose proof HB as (Hafn & _ & _ & HSAlo & HSAhi & _ & _ & _ & _ & Hj & _).
change AENT with 56 in HSAhi. change ATABLE with 896 in HSAhi.
pose proof Hafn as (_ & _ & _ & _ & _ & (_ & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hslo, Hshi.
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof HGSB as (GS1 & GS2 & GS3). unfold IMG_TOP in GS2.
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
pose proof pa_segs_low as Hsegs.
pose proof HEOK as (_ & _ & Hp1 & Hp2 & _ & _ & _ & Husedc & _).
(* the blocks: the pending list's (AP) and the rest (Lr) *)
pose proof (dd_perm_split (dxG cx, ATABLE) (hs_partial h1, APARTIAL) (aentry_blks e1) (alist_blks (hs_pending h1))
  (alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) (aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx)) as PL.
fold (asrc_blks h1) in PL.
set (Lr := aentry_blks e1 ++ ((hs_partial h1, APARTIAL) :: alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) ++
  aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) in PL.
set (AP := alist_blks (hs_pending h1)) in PL.
pose proof (Permutation_trans Hperm PL) as HP1.
assert (INL1 : forall b, In b ((dxG cx, ATABLE) :: Lr ++ AP) -> In b (ablocks B ly1 S1))
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HP1) Hb)).
assert (ND : List.NoDup (map fst ((dxG cx, ATABLE) :: Lr ++ AP))).
{ apply (df_pu_nd B LAWS ly1 S1 W1 m1 md1 _ [] [] HAR1). rewrite app_nil_r. exact HP1. }
assert (NDG : ~ In (dxG cx) (map fst (Lr ++ AP))).
{ cbn [map] in ND. inversion ND; subst. assumption. }
assert (NDL : forall b, In b Lr -> ~ In (fst b) (map fst AP)).
{ intros b Hb. cbn [map] in ND. inversion ND as [|z l Hz Hl]; subst. exact (dd_nd_fst2 Lr AP b Hl Hb). }
assert (GT : In (dxG cx, ATABLE) (ablocks B ly1 S1)) by (apply INL1; left; reflexivity).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR1 GT) as (_ & HG4 & HGc & _).
change (req_size ATABLE) with 896 in HGc.
assert (INAP : forall b, In b AP -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply INL1; right; apply in_or_app; right; exact Hb).
assert (HXB' : forall a, XB a -> exists p q, In (p, q) AP /\ In (p, q) (ablocks B ly1 S1) /\
  p <= a < p + req_size q /\ p + req_size q <= alloc_ceiling /\ ~ in_img SEGS a).
{ intros a Ha. destruct (HXB a Ha) as (p & q & Hin & Hpa). pose proof (INAP _ Hin) as Hab.
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 p q HAR1 Hab) as (_ & _ & Hc & _).
  exists p, q. split; [exact Hin|]. split; [exact Hab|]. split; [exact Hpa|]. split; [exact Hc|].
  exact (proj2 (al_client_img SEGS B LAWS ly1 S1 W1 m1 md1 a HAR1
    (or_introl (ex_intro _ p (ex_intro _ q (conj Hab Hpa)))))). }
assert (TNI : forall a, dxG cx <= a < dxG cx + 896 -> ~ in_img SEGS a).
{ intros a Ha. assert (Hb : dxG cx <= a < dxG cx + req_size ATABLE) by (change (req_size ATABLE) with 896; lia).
  exact (proj2 (al_client_img SEGS B LAWS ly1 S1 W1 m1 md1 a HAR1
    (or_introl (ex_intro _ (dxG cx) (ex_intro _ ATABLE (conj GT Hb)))))). }
assert (GSI : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. destruct (df_pu_gs B RG HRGD a Ha) as (Hin & He). destruct (HG a Hin) as (Hi & Ho & _).
  split; [exact Hi|]. split; [exact Ho | exact He]. }
(* a byte of a block of Lr is off ddX *)
assert (NX : forall p q a, In (p, q) Lr -> p <= a < p + req_size q -> ~ ddX cx lo XB a).
{ intros p q a Hin Ha. assert (Hab : In (p, q) (ablocks B ly1 S1)) by (apply INL1; right; apply in_or_app; left; exact Hin).
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 p q HAR1 Hab) as (_ & _ & Hc & _).
  pose proof (proj2 (al_client_img SEGS B LAWS ly1 S1 W1 m1 md1 a HAR1
    (or_introl (ex_intro _ p (ex_intro _ q (conj Hab Ha)))))) as Hni.
  assert (HpG : p <> dxG cx).
  { intros E. apply NDG. rewrite map_app. apply in_or_app. left. rewrite <- E.
    exact (in_map fst Lr (p, q) Hin). }
  pose proof (NDL (p, q) Hin) as HpAP. cbn [fst] in HpAP.
  unfold ddX. intros [Hx | [Hx | [Hx | Hx]]].
  - apply Hni. apply (GSI a). unfold ASRC in *; lia.
  - apply (df_lp_rq_out B LAWS ly1 S1 W1 m1 md1 p q (dxG cx) ATABLE a HAR1 Hab GT HpG Ha).
    change (req_size ATABLE) with 896. lia.
  - destruct (HXB' a Hx) as (p' & q' & Hin' & Hab' & Ha' & _).
    assert (Hne : p <> p') by (intros E; apply HpAP; rewrite E; exact (in_map fst AP (p', q') Hin')).
    exact (df_lp_rq_out B LAWS ly1 S1 W1 m1 md1 p q p' q' a HAR1 Hab Hab' Hne Ha Ha').
  - lia. }
(* a byte of the table outside s->used, and an image byte outside g_s[j]'s 16..40, are off ddX *)
assert (NT : forall a, dxSA cx <= a < dxSA cx + 56 -> ~ (dxSA cx + 24 <= a < dxSA cx + 32) -> ~ ddX cx lo XB a).
{ intros a Ha Hn. pose proof (TNI a ltac:(lia)) as Hni.
  unfold ddX. intros [Hx | [Hx | [Hx | Hx]]].
  - apply Hni. apply (GSI a). unfold ASRC in *; lia.
  - exact (Hn Hx).
  - destruct (HXB' a Hx) as (p' & q' & Hin' & Hab' & Ha' & _).
    assert (Hne : dxG cx <> p').
    { intros E. apply NDG. rewrite map_app. apply in_or_app. right. rewrite E. exact (in_map fst AP (p', q') Hin'). }
    apply (df_lp_rq_out B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE p' q' a HAR1 GT Hab' Hne); [|exact Ha'].
    change (req_size ATABLE) with 896. lia.
  - lia. }
assert (NI : forall a, in_img SEGS a -> ~ (dHA RG cx + 16 <= a < dHA RG cx + 40) -> ~ ddX cx lo XB a).
{ intros a Hi Hn. pose proof (Hsegs a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  unfold ddX. intros [Hx | [Hx | [Hx | Hx]]].
  - exact (Hn Hx).
  - exact (TNI a ltac:(lia) Hi).
  - destruct (HXB' a Hx) as (_ & _ & _ & _ & _ & _ & Hni). exact (Hni Hi).
  - lia. }
(* the new block list *)
pose proof (dd_perm_drop (dxG cx, ATABLE) (hs_partial h1, APARTIAL) (aentry_blks e1)
  (if hl_cap (hs_pending h1) =? 0 then [] else [(hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1))])
  (map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) pre)
  (map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l2))
  (alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) (aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx)) as PD.
assert (EAP : AP = (if hl_cap (hs_pending h1) =? 0 then [] else [(hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1))]) ++
  map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) pre ++
  map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l2))
  by (unfold AP, alist_blks; rewrite Erecs, map_app; reflexivity).
rewrite <- EAP in PD. fold Lr in PD.
assert (EA2 : asrc_blks (dd_hset h1 l2 off2) = (hs_partial h1, APARTIAL) ::
  ((if hl_cap (hs_pending h1) =? 0 then [] else [(hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1))]) ++
   map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l2)) ++
  alist_blks (hs_expected h1) ++ alist_blks (hs_held h1))
  by (unfold asrc_blks, dd_hset, alist_blks; cbn [hs_partial hs_pending hs_expected hs_held]; rewrite Ev, Ec; reflexivity).
rewrite <- EA2 in PD.
assert (HP2 : Permutation (ablocks B ly2 S2)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dd_hset h1 l2 off2) ++ aout_blks (drain_b_c.ds_ocap s) out ++
   dxrest cx)).
{ apply (Permutation_app_inv_l (map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) pre)).
  eapply Permutation_trans; [apply Permutation_sym; exact HPm|]. eapply Permutation_trans; [exact HP1|]. exact PD. }
assert (INL2 : forall b, In b ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dd_hset h1 l2 off2) ++
  aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) -> In b (ablocks B ly2 S2))
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HP2) Hb)).
assert (GT2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)) by (apply INL2; left; reflexivity).
(* what is kept *)
assert (KBL : forall p q a, In (p, q) Lr -> p <= a < p + req_size q -> abyte_kept W1 m1 W2 m2 a).
{ intros p q a Hin Ha. assert (Hab : In (p, q) (ablocks B ly1 S1)) by (apply INL1; right; apply in_or_app; left; exact Hin).
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 p q HAR1 Hab) as (_ & H4 & Hc & _).
  apply KX; [pose proof (@YM05.alloc_ceiling_lt rc) as ACL; lia | exact (NX p q a Hin Ha)
    | left; exists p, q; split; [exact Hab | exact Ha]]. }
assert (KF : forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha. apply KX; [lia | | right; right; exact Ha]. unfold ddX. intros [Hx | [Hx | [Hx | Hx]]].
  - unfold ASRC in *. lia.
  - lia.
  - destruct (HXB' a Hx) as (p' & q' & _ & _ & Ha' & Hc & _). lia.
  - lia. }
assert (KG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= a < dHA RG cx + ASRC) ->
  abyte_kept W1 m1 W2 m2 a).
{ intros a Ha Hn. pose proof (proj1 (GSI a Ha)) as Hi. pose proof (Hsegs a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  destruct (GSI a Ha) as (_ & Ho & _).
  apply KX; [lia | apply NI; [exact Hi | unfold ASRC in *; lia] | right; left; split; [exact Hi | exact Ho]]. }
assert (KO : akept W1 m1 W2 m2 (aout_fp B RG (drain_b_c.ds_ocap s) out)).
{ assert (CELL : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (rg_s RG <= a < rg_s RG + 4 * ASRC) -> abyte_kept W1 m1 W2 m2 a).
  { intros a Hi Ho Hn. pose proof (Hsegs a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    apply KX; [lia | apply NI; [exact Hi | unfold ASRC in *; lia] | right; left; split; [exact Hi | exact Ho]]. }
  intros r Hr a Ha. unfold aout_fp in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha;
    try (destruct (df_cell_facts B RG HGO HRGD a ltac:(lia)) as (_ & Hn & Hi & Ho & _); exact (CELL a Hi Ho Hn));
    try (destruct (df_pu_sl B RG HRGD a ltac:(lia)) as (Hin & _ & Hn);
         exact (CELL a (proj1 (HG a Hin)) (proj1 (proj2 (HG a Hin))) Hn));
    try (assert (HeG : inG (G_DR B RG) a)
           by (unfold G_DR, G_SL, inG; do 6 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia);
         destruct (df_errno_facts B RG HG HRGD a ltac:(lia)) as (_ & Hn & Hi);
         exact (CELL a Hi (proj1 (proj2 (HG a HeG))) Hn)).
  destruct (drain_b_c.ds_ocap s =? 0) eqn:Ec0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []].
  cbn [fst snd] in Ha.
  assert (Hin : In (out, drain_b_c.ds_ocap s) Lr).
  { unfold Lr. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. unfold aout_blks. rewrite Ec0.
    left. reflexivity. }
  apply Z.eqb_neq in Ec0.
  assert (Hab : In (out, drain_b_c.ds_ocap s) (ablocks B ly1 S1)) by (apply INL1; right; apply in_or_app; left; exact Hin).
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 Hab) as (_ & _ & _ & _ & _ & _ & Hn0').
  pose proof (req_size_pos (drain_b_c.ds_ocap s) (proj1 Hn0')) as (_ & Hrq).
  apply (KBL out (drain_b_c.ds_ocap s) a Hin). lia. }
(* the new entry *)
assert (KSA : forall y, dxSA cx <= y < dxSA cx + 56 -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
  aview SEGS (w_H W2) m2 y = aview SEGS (w_H W1) m1 y).
{ intros y Hy Hn.
  assert (HyK : ddK ly1 S1 cx y)
    by (left; exists (dxG cx), ATABLE; split; [exact GT | change (req_size ATABLE) with 896; lia]).
  apply (proj1 (KX y ltac:(lia) (NT y Hy Hn) HyK)). }
assert (Hent2 : garr8 SEGS (arm W2 m2) (dxSA cx) (bzs (entry_bytes (dd_eadd e1 n)))).
{ unfold dd_eadd. apply (dd_entry_set W1 W2 m1 m2 (dxSA cx) e1 (re_used e1 + n) Hgarr Hp1 Hp2 KSA Vu).
  pose proof HEOK as (_ & _ & _ & _ & _ & Hcr & HUl & _ & Hbj & _).
  destruct Hbj as [(Hc0 & _) | (_ & _ & Hjl & _)]; [lia|].
  destruct Hcr as [H | [H | H]]; lia. }
assert (Hawr2 : awr W2 m2 (dxSA cx) AENT).
{ intros i Hi. unfold AENT in Hi. replace (dxSA cx + i) with (dxG cx + (dxSA cx - dxG cx + i)) by lia.
  apply (df_blk_wr B LAWS ly2 S2 W2 m2 md2 (dxG cx) ATABLE HAR2 GT2). change (req_size ATABLE) with 896. lia. }
assert (Hokx2 : aentry_okx B ly2 S2 W2 m2 (dd_eadd e1 n)).
{ apply (dd_aentry_add ly2 S2 W2 m2 e1 n); [| exact Hcp | exact Hn0 | exact Hnj].
  apply (df_aentry_okx_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 e1 HEOK).
  - apply (df_pu_aentry_kept B RG ly1 S1 W1 W2 m1 m2 e1 HEOK). intros p q a Hin Ha.
    apply (KBL p q a); [unfold Lr; apply in_or_app; left; exact Hin | exact Ha].
  - intros b Hb. apply INL2. right. apply in_or_app. left. exact Hb. }
(* the new source *)
assert (Hsrc2 : asrc_at B ly2 S2 W2 m2 (dHA RG cx) (dd_hset h1 l2 off2)).
{ apply (dd_asrc_set ly1 S1 W1 m1 md1 ly2 S2 W2 m2 (dHA RG cx) h1 l2 off2 pre HAR1 Hsrc);
    [ | | | | exact HL2 | exact Ev | exact Ec | exact Erecs | exact Voff | exact Hoff].
  - intros a Ha Hn. pose proof (GSI a ltac:(unfold ASRC in *; lia)) as (Hi & Ho & _).
    pose proof (Hsegs a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    apply KX; [lia | exact (NI a Hi Hn) | right; left; split; [exact Hi | exact Ho]].
  - intros p q a Hin Ha. apply (KBL p q a); [|exact Ha].
    unfold Lr. apply in_or_app. right. apply in_or_app. left. exact Hin.
  - intros b Hb. apply INL2. right. apply in_or_app. right. apply in_or_app. left. rewrite EA2.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right. apply in_or_app. right. exact Hb.
  - pose proof Hsrc as (_ & _ & _ & _ & HAW1 & _). intros i Hi.
    destruct (GSI (dHA RG cx + i) ltac:(unfold ASRC in *; lia)) as (Hi' & Ho & He).
    apply (df_wr_img W1 W2 m1 m2 (dHA RG cx + i) Hi' (HPK2 _ Hi' Ho He) (HAW1 i Hi)). }
exact (dd_dmem_close cx ly1 S1 W1 m1 md1 k1 e1 h1 s out ev sent LB ly2 S2 W2 m2 md2 k2 (dd_eadd e1 n)
  (dd_hset h1 l2 off2) HM HJ2 Hrv2 HPK2 HFR2 KF Hent2 Hawr2 Hokx2 KG KO Hsrc2 HP2).
Qed.

(* ------------------------------------------------------------------ DJ at p = 0 from DE's model *)
(* lib/B/W_drain_join.v's cut DJ at p = 0: the virtual state of the round is dvirt at p = 0 (no line before p, so
   no / oc / H / ka are the round's own), the relay's buffer holds U ++ d (DE's n junk bytes moved into U), and the
   source is the one DROP leaves (pending list and pending_off replaced).  Every model conjunct is DE's. *)
Lemma dd_DJ : forall cx s1 D regs2 ly2 S2 (W2 : world SEGS) m2 md2 k2 e1 h1 l2 off2 out1 ev1 LB1 spent2
  jb a o ha ks tl2,
dregs_line RG cx regs2 W2 m2 -> getr regs2 26 = w64 DR_SCAN_END -> getr regs2 24 = w64 (re_buf e1) ->
dinband (re_buf e1) (re_cap e1) ->
DMEM B RG cx ly2 S2 W2 m2 md2 k2 (dd_eadd e1 (dnum s1)) (dd_hset h1 l2 off2) s1 out1 ev1 (lines (dSTR cx) D) LB1 ->
bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 ->
DSAME cx e1 h1 ->
re_cap e1 = drain_b_c.ds_cap s1 -> bzs (re_U e1) = drain_b_c.ds_u s1 ->
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) ->
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 -> drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 ->
hs_eintr h1 = 0 ->
hs_state h1 = feed (drain_b_c.ds_ref s1) (ddata s1) ->
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) ->
hl_cap (hs_expected h1) = pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) ->
DHIST cx s1 D (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
RSTART cx s1 D ->
hl_v l2 = hl_v (hs_pending h1) -> hl_cap l2 = hl_cap (hs_pending h1) ->
map (fun r => bzs (snd r)) (hl_recs l2) = (if dwhole s1 then dtail s1 else drain_b_c.ds_pend s1) ->
off2 = (if dwhole s1 then 0 else drain_b_c.ds_off s1 + dnum s1) ->
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1) (drain_b_c.ds_H s1)
  (drain_b_c.ds_ka s1) (drl s1) jb o ha ks tl2 ->
dbud MT MMAX cx S2 spent2 tl2 ->
DJ B MT MMAX RG cx s1 D 0 W2 (cfg_at SEGS (BASE + A_dr_join) regs2 m2 md2).
Proof.
intros cx s1 D regs2 ly2 S2 W2 m2 md2 k2 e1 h1 l2 off2 out1 ev1 LB1 spent2 jb a o ha ks tl2
  HRG R26 R24 HDB HM Hjunk HSAME Hcap HU Hsk HHk Hka Hei Hst Hen Hec HH HRS Ev Ec Erecs Eoff HFUT HBUD.
pose proof HRS as (Href & (_ & _ & _ & HNZ) & H4096 & Hdwf & _ & _ & Hpne).
pose proof Hdwf as (Hoff0 & Hoffl).
assert (HD : 0 <= dnum s1 /\ drain_b_c.ds_off s1 + dnum s1 <= Z.of_nat (length (dhead s1))).
{ unfold dnum, dhead, ulen in *. destruct (drain_b_c.ds_pend s1) as [|r rs] eqn:Ep; [congruence|].
  specialize (Hoffl r rs eq_refl). lia. }
destruct HD as (Hn0 & Hnl).
pose proof (dd_pstream s1 Hoff0 Hn0 Hnl) as HPS.
pose proof (dd_dwf_next s1 Hoff0 Hn0 Hnl) as HWN.
pose proof (dd_drl_len s1 HNZ) as HRL.
pose proof (dd_lines_len (ddata s1) (drain_b_c.ds_ref s1)) as HLL.
assert (HULEN : 0 <= ulen s1) by (unfold ulen; lia).
set (sv := dvirt cx s1 (dskp s1 0) (dlH cx s1 0) (dlka cx s1 0) (dlno s1 0) (dloc cx s1 0)).
assert (SNO : drain_b_c.ds_no sv = drain_b_c.ds_no s1) by (unfold sv, dvirt; cbn [drain_b_c.ds_no]; apply dd_dlno0).
assert (SOC : drain_b_c.ds_ocap sv = drain_b_c.ds_ocap s1) by reflexivity.
assert (SPS : pstream sv = prest (if dwhole s1 then dtail s1 else drain_b_c.ds_pend s1)
  (if dwhole s1 then 0 else drain_b_c.ds_off s1 + dnum s1)) by reflexivity.
exists regs2, ly2, S2, m2, md2, k2, (dd_eadd e1 (dnum s1)), (dd_hset h1 l2 off2), out1, ev1, LB1, spent2,
  jb, a, o, ha, ks, tl2.
split; [reflexivity|].
split; [exact HRG|]. split; [exact R26|].
split; [unfold dd_eadd, drr_eset; cbn [re_buf]; rewrite Z.add_0_r; exact R24|].
split; [unfold dd_eadd, drr_eset; cbn [re_buf re_cap]; exact HDB|].
split; [unfold dd_eadd, drr_eset; cbn [re_cap]; lia|].
split; [unfold dbound; split; [lia | left; reflexivity]|].
split.
- unfold DLC, LCORE. fold sv. rewrite dd_drlp0, app_nil_r.
  split; [exact (drr_DMEM_s B RG cx _ _ _ _ _ _ _ _ s1 sv _ _ _ _ SNO SOC HM)|].
  split.
  { unfold DLINK, dd_eadd, drr_eset, dd_hset, drain_b_c.ent_ka in *.
    cbn [re_cap re_U re_skip re_keys re_hp re_kh hs_eintr hs_pending hs_off hs_expected].
    unfold sv, dvirt, dnext. cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
      drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap].
    split; [exact Hcap|].
    split; [unfold bzs; rewrite map_app; fold (bzs (re_U e1)); fold (bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)));
      rewrite HU, Hjunk; reflexivity|].
    split; [exact Hsk|]. split; [exact HHk|]. split; [exact Hka|]. split; [rewrite Hei; reflexivity|].
    split; [exact Erecs|]. split; [exact Eoff|]. split; [exact Hst|].
    split; [exact Hen|]. split; [exact Hec|].
    unfold dwf. cbn [drain_b_c.ds_off drain_b_c.ds_pend]. exact HWN. }
  split.
  { unfold DSAME, dd_eadd, drr_eset, dd_hset in *.
    cbn [re_fd re_eof re_hp re_kh hs_fd hs_open hs_closed hs_pending hs_partial hs_held].
    rewrite Ev, Ec. exact HSAME. }
  split.
  { destruct HH as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
    unfold DHIST. unfold dd_hset. cbn [hs_expected].
    split; [rewrite P1, HPS, SPS, app_assoc; reflexivity|].
    split; [unfold sv, dvirt, dnext; cbn [drain_b_c.ds_ref]; rewrite P2, feed_app; reflexivity|].
    split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
    split; [rewrite SNO; exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
    split.
    - change (drain_b_c.ds_H sv) with (drain_b_c.ds_H s1). rewrite (dd_drlq0 s1 HNZ).
      rewrite HPS, length_app in P10. rewrite <- SPS in P10. lia.
    - assert (SEN : drain_b_c.ds_en sv = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1))) by reflexivity.
      rewrite SEN. unfold dref in *.
      rewrite HPS, length_app in P11. rewrite <- SPS in P11. lia. }
  split; [exact HRS | exact HBUD].
- rewrite dd_dlno0, (dd_drlq0 s1 HNZ).
  change (dloc cx s1 0) with (drain_b_c.ds_ocap s1). change (dlH cx s1 0) with (drain_b_c.ds_H s1).
  change (dlka cx s1 0) with (drain_b_c.ds_ka s1). exact HFUT.
Qed.

End c.

(* ---- THE GENERIC BOOKKEEPING (an internal work row, slice B): DROP's model and memory bookkeeping over any allocator relation
   ARx with its laws, at the room texts.  The Section's variables are W_drain_cx_x.v's Section c's, B PST ARx MT RP
   MMAX RG in that order; its hypotheses are lib/B/W_drain_drop.v Section cx's in the same order (that file's walk
   cites the lemmas below with this Section's hypotheses taken from its own), less the facts only the walk reads:
   after LAWS the generic-relation facts the bookkeeping reads, at the texts shared across the slices,
     BLKN (a live block's size is >= 0: AR's al_blocks carries it, ARx_blocks_law does not);
     PSTG / PSTO (g_s and aout_at's cells lie off the placement PST: a callee's journal keeps an image byte only off
     PST, YCbqG.ajournal_x's image clause);
   then W_drain_cx_x.v Section c's hypotheses, its text.
   The AR bookkeeping (Section c) is unchanged.  Its Definitions and its AR-free lemmas are cited; each lemma that
   reads AR, DBASE, DMEM or ajournal_gx is restated here with an _x suffix, and the block facts over ARx they read are
   lib/B/W_drain_feed.v Section cx's (df_pu_nd_x, df_lp_rq_out_x, df_blk_wr_x), cited.  ddK_x is ddK with its image
   disjunct off PST: the list_drop call (lib/B/W_drain_drop.v Section cx) keeps an image byte only off PST, and every
   image byte dd_arm_close_x asks for (g_s, aout_at's cells) is off PST by PSTG / PSTO. ---- *)
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
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis PSTG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ Exists (in_zr a) PST.
Hypothesis PSTO : forall a, inG (G_SL B RG) a \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a ->
  ~ Exists (in_zr a) PST.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Variable CTX_F : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
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

(* a cell of a listed G (a range list) holds the address a: the list's position is found by lia *)
Local Ltac ddx_inG := unfold inG; solve [repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]].

(* ---- dd_asrc_set (Section c) over ARx: its AR premise becomes the ARx one (the proof reads neither) ---- *)
Lemma dd_asrc_set_x : forall ly1 S1 Hp1 (W1 : world SEGS) m1 md1 ly2 S2 (W2 : world SEGS) m2 HA h1 l2 off2 pre,
ARx ly1 S1 Hp1 W1 m1 md1 ->
asrc_at B ly1 S1 W1 m1 HA h1 ->
(forall a, HA <= a < HA + ASRC -> ~ (HA + 16 <= a < HA + 40) -> abyte_kept W1 m1 W2 m2 a) ->
(forall p n a, In (p, n) ((hs_partial h1, APARTIAL) :: alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) ->
   p <= a < p + req_size n -> abyte_kept W1 m1 W2 m2 a) ->
(forall b, In b ((hs_partial h1, APARTIAL) :: alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) ->
   In b (ablocks B ly2 S2)) ->
awr W2 m2 HA ASRC ->
alist_at B ly2 S2 W2 m2 (HA + 16) l2 false ->
hl_v l2 = hl_v (hs_pending h1) -> hl_cap l2 = hl_cap (hs_pending h1) ->
hl_recs (hs_pending h1) = pre ++ hl_recs l2 ->
val_mem SEGS (arm W2 m2) (HA + 32) 8 off2 ->
((hl_recs l2 = [] /\ off2 = 0) \/ (exists r rs, hl_recs l2 = r :: rs /\ 0 <= off2 < Z.of_nat (length (snd r)))) ->
asrc_at B ly2 S2 W2 m2 HA (dd_hset h1 l2 off2).
Proof.
intros ly1 S1 Hp1 W1 m1 md1 ly2 S2 W2 m2 HA h1 l2 off2 pre HAR HS KH KB HBL HAW HL2 Ev Ec Erecs Voff Hoff.
pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & H24).
assert (VH : forall a n v, HA <= a -> a + Z.of_nat n <= HA + ASRC -> (a + Z.of_nat n <= HA + 16 \/ HA + 40 <= a) ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W2 m2) a n v).
{ intros a n v Ha Hn Hd Hv. apply (akept_vm W1 m1); [|exact Hv]. intros x Hx. apply KH; lia. }
assert (LK : forall LA l lines, HA + 40 <= LA -> LA + 16 <= HA + ASRC ->
  (forall b, In b (alist_blks l) ->
     In b ((hs_partial h1, APARTIAL) :: alist_blks (hs_expected h1) ++ alist_blks (hs_held h1))) ->
  alist_at B ly1 S1 W1 m1 LA l lines -> alist_at B ly2 S2 W2 m2 LA l lines).
{ intros LA l lines HL1 HL2' Hsub HL. apply (alist_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 LA l lines HL).
  - apply (df_pu_alist_kept B RG ly1 S1 W1 W2 m1 m2 LA l lines HL).
    + intros a Ha. apply KH; unfold ASRC in *; lia.
    + intros p n a Hpn Ha. exact (KB p n a (Hsub _ Hpn) Ha).
  - intros b Hb. exact (HBL b (Hsub b Hb)). }
unfold asrc_at, dd_hset.
cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
  hs_expected hs_held].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H1]|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H2]|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H3]|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H4]|].
split; [exact HAW|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
split; [exact HL2|].
split; [exact Voff|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H12]|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H13]|].
split; [apply VH; [lia | cbn; unfold ASRC; lia | cbn; lia | exact H14]|].
split; [exact Hoff|].
split; [exact H16|]. split; [exact H17|].
split; [apply HBL; left; reflexivity|].
split; [exact H19|].
split.
{ apply (akept_garr8 W1 m1); [|exact H20]. intros x Hx. apply (KB (hs_partial h1) APARTIAL x); [left; reflexivity|].
  unfold bzs in Hx. rewrite length_map, H19 in Hx.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia. }
split; [exact H21|].
split; [apply (LK (HA + 64) _ true); [lia | unfold ASRC; lia
  | intros b Hb; right; apply in_or_app; left; exact Hb | exact H22]|].
split; [apply (LK (HA + 80) _ true); [lia | unfold ASRC; lia
  | intros b Hb; right; apply in_or_app; right; exact Hb | exact H23]|].
apply (proj2 (stdpp.base.NoDup_ListNoDup _)). apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in H24.
unfold hs_blocks, list_blocks in H24 |- *.
cbn [hs_fd hs_open hs_closed hs_eintr hs_pending hs_off hs_partial hs_pjunk hs_npartial hs_overlong hs_pad
  hs_expected hs_held] in H24 |- *.
rewrite Ev, Ec. rewrite Erecs, map_app in H24. rewrite <- !app_assoc in H24.
pose proof (dd_nodup_mid _ _ (map fst pre) _ H24) as X. rewrite <- ?app_assoc in X. rewrite <- ?app_assoc. exact X.
Qed.

(* ---- dd_dmem_close (Section c) over DMEM_x and the generic journal ---- *)

(* ---- DMEM_x after DROP ---- *)
(* ddK (Section c) with its image disjunct off PST *)
Definition ddK_x (ly : alayout) (S : astate) (cx : dcx) (a : Z) : Prop :=
(exists p q, In (p, q) (ablocks B ly S) /\ p <= a < p + req_size q) \/
(in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ Exists (in_zr a) PST) \/
(dsp0 cx - DRAIN_FRAME <= a < dsp0 cx).


(* ---- DJ_x at p = 0 from DE_x's model ---- *)
(* lib/B/W_drain_rest.v drr_DMEM_s over DMEM_x: DMEM_x reads the round state only through ds_no and ds_ocap *)

(* dd_DJ (Section c) at the generic cut: DJ_x (lib/B/W_drain_join.v Section cx) at p = 0, the cut's ghost list Hp2 and
   its budget dbud_x; every model conjunct is DE_x's *)


(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twin of each relation-dependent lemma above.  Each
   twin is its strict text with the journal and the step relation at R: ajournal_gx_x -> ajournal_gx_xR .. R,
   SRr SEGS -> SRrG SEGS R, the runs and the branch are their SRrG forms (W_journal_x.v paj_run_x_xG /
   paj_run_to_x_xG, W_kit.v paj_branch_xR), each carrier X_x -> its twin X_xR (R last), the journal lemmas their _xR
   forms, and each lemma name L -> LR; the relation-free helpers above are cited as they are.  The strict text is
   untouched. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.

Lemma dd_dmem_close_xR : forall cx Hp ly S Hp1 W m md k e h s out ev sent LB ly' S' Hp1' W' m' md' k' e' h',
DMEM_xR B PST ARx RG R cx Hp ly S Hp1 W m md k e h s out ev sent LB ->
ajournal_gx_xR SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly' S' Hp1' W' m' md' k' ->
rom_view SEGS W' m' -> apres_kept B W m W' m' -> frames S' = frames S ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
garr8 SEGS (arm W' m') (dxSA cx) (bzs (entry_bytes e')) -> awr W' m' (dxSA cx) AENT ->
aentry_okx B ly' S' W' m' e' ->
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= a < dHA RG cx + ASRC) ->
   abyte_kept W m W' m' a) ->
akept W m W' m' (aout_fp B RG (drain_b_c.ds_ocap s) out) ->
asrc_at B ly' S' W' m' (dHA RG cx) h' ->
Permutation (ablocks B ly' S')
  ((dxG cx, ATABLE) :: aentry_blks e' ++ asrc_blks h' ++ aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) ->
DMEM_xR B PST ARx RG R cx Hp ly' S' Hp1' W' m' md' k' e' h' s out ev sent LB.
Proof.
intros cx Hp ly S Hp1 W m md k e h s out ev sent LB ly' S' Hp1' W' m' md' k' e' h' HD HJ' KR KP KF KS Hent' Hawr' Hokx'
  KG KO HS' HP'.
destruct HD as (HJ & Hrom & Hpres & Hfr & HFR & Hent & Hawr & Hokx & Hsrc & Hoth & Hgsk & Hout & Hlive & Hperm).
assert (HIN : forall b, In b (aout_blks (drain_b_c.ds_ocap s) out) -> In b (ablocks B ly' S')).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HP'|]. right.
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (VK : forall a n v, dsp0 cx - DRAIN_FRAME <= a -> a + Z.of_nat n <= dsp0 cx ->
  val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W' m') a n v).
{ intros a n v H1 H2 Hv. apply (akept_vm W m); [intros x Hx; apply KS; lia | exact Hv]. }
split; [exact HJ'|].
split; [exact KR|].
split; [intros a H1 H2 H3 H4; exact (KP a H1 H2 H3 (Hpres a H1 H2 H3 H4))|].
split; [rewrite KF; exact Hfr|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 &
    F18 & F19 & F20 & F21 & F22 & F23 & FS).
  unfold DRAIN_FRAME in VK |- *.
  repeat split; try (apply VK; [simpl Z.of_nat; lia | simpl Z.of_nat; lia | assumption]).
  unfold dr_saved, DR_SAVE_OFF. intros i Hi. apply VK; [lia | simpl Z.of_nat; lia | exact (FS i Hi)]. }
split; [exact Hent'|].
split; [exact Hawr'|].
split; [exact Hokx'|].
split; [exact HS'|].
split.
{ intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & V1 & V2 & Vo). exists f, o.
  assert (KI : forall x, rg_s RG + ASRC * Z.of_nat i <= x < rg_s RG + ASRC * Z.of_nat i + 8 ->
    abyte_kept W m W' m' x).
  { intros x Hx. apply KG; unfold dHA, ASRC in *; [lia|]. intros Hc. apply Hij. lia. }
  split; [|split; [|exact Vo]]; (apply (akept_vm W m); [intros x Hx; apply KI; simpl Z.of_nat in Hx; lia|]);
  assumption. }
split; [intros x Hx1 Hx2; exact (df_bk_trans _ _ _ _ _ _ x (Hgsk x Hx1 Hx2) (KG x Hx1 Hx2))|].
split; [exact (aout_at_kept B RG ly S W m ly' S' W' m' _ _ _ _ _ _ Hout KO HIN)|].
split; [exact Hlive | exact HP'].
Qed.

Lemma dd_arm_close_xR : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 s out ev sent LB
  ly2 S2 Hp2 (W2 : world SEGS) m2 md2 k2 lo XB l2 off2 pre n,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out ev sent LB ->
ajournal_gx_xR SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 k2 ->
rom_view SEGS W2 m2 -> apres_kept B W1 m1 W2 m2 -> frames S2 = frames S1 ->
alloc_ceiling <= lo ->
(forall a, XB a -> exists p q, In (p, q) (alist_blks (hs_pending h1)) /\ p <= a < p + req_size q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ ddX RG cx lo XB a -> ddK_x ly1 S1 cx a -> abyte_kept W1 m1 W2 m2 a) ->
alist_at B ly2 S2 W2 m2 (dHA RG cx + 16) l2 false ->
hl_v l2 = hl_v (hs_pending h1) -> hl_cap l2 = hl_cap (hs_pending h1) ->
hl_recs (hs_pending h1) = pre ++ hl_recs l2 ->
Permutation (ablocks B ly1 S1)
  (map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) pre ++ ablocks B ly2 S2) ->
val_mem SEGS (arm W2 m2) (dHA RG cx + 32) 8 off2 ->
((hl_recs l2 = [] /\ off2 = 0) \/ (exists r rs, hl_recs l2 = r :: rs /\ 0 <= off2 < Z.of_nat (length (snd r)))) ->
val_mem SEGS (arm W2 m2) (dxSA cx + 24) 8 (re_used e1 + n) ->
0 <= n -> n <= Z.of_nat (length (re_junk e1)) -> 0 < re_cap e1 ->
DMEM_xR B PST ARx RG R cx Hp ly2 S2 Hp2 W2 m2 md2 k2 (dd_eadd e1 n) (dd_hset h1 l2 off2) s out ev sent LB.
Proof.
intros cx Hp kr ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out ev sent LB ly2 S2 Hp2 W2 m2 md2 k2 lo XB l2 off2 pre n
  HB HM HJ2 Hrv2 HPK2 HFR2 Hlo HXB KX HL2 Ev Ec Erecs HPm Voff Hoff Vu Hn0 Hnj Hcp.
pose proof HM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
pose proof HB as (Hafn & _ & _ & HSAlo & HSAhi & _ & _ & _ & _ & Hj & _).
change AENT with 56 in HSAhi. change ATABLE with 896 in HSAhi.
pose proof Hafn as (_ & _ & _ & _ & _ & (_ & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hslo, Hshi.
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HDSx : DRAIN_STK_x = 17008) by reflexivity.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof HGSB as (GS1 & GS2 & GS3). unfold IMG_TOP in GS2.
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
pose proof pa_segs_low as Hsegs.
pose proof HEOK as (_ & _ & Hp1' & Hp2' & _ & _ & _ & Husedc & _).
(* the blocks: the pending list's (AP) and the rest (Lr) *)
pose proof (dd_perm_split (dxG cx, ATABLE) (hs_partial h1, APARTIAL) (aentry_blks e1) (alist_blks (hs_pending h1))
  (alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) (aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx)) as PL.
fold (asrc_blks h1) in PL.
set (Lr := aentry_blks e1 ++ ((hs_partial h1, APARTIAL) :: alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) ++
  aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) in PL.
set (AP := alist_blks (hs_pending h1)) in PL.
pose proof (Permutation_trans Hperm PL) as HP1.
assert (INL1 : forall b, In b ((dxG cx, ATABLE) :: Lr ++ AP) -> In b (ablocks B ly1 S1))
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HP1) Hb)).
assert (ND : List.NoDup (map fst ((dxG cx, ATABLE) :: Lr ++ AP))).
{ apply (df_pu_nd_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 _ [] [] HAR1). rewrite app_nil_r. exact HP1. }
assert (NDG : ~ In (dxG cx) (map fst (Lr ++ AP))).
{ cbn [map] in ND. inversion ND; subst. assumption. }
assert (NDL : forall b, In b Lr -> ~ In (fst b) (map fst AP)).
{ intros b Hb. cbn [map] in ND. inversion ND as [|z l Hz Hl]; subst. exact (dd_nd_fst2 Lr AP b Hl Hb). }
assert (GT : In (dxG cx, ATABLE) (ablocks B ly1 S1)) by (apply INL1; left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR1 GT) as (_ & HG4 & HGc & _).
change (req_size ATABLE) with 896 in HGc.
assert (INAP : forall b, In b AP -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply INL1; right; apply in_or_app; right; exact Hb).
assert (HXB' : forall a, XB a -> exists p q, In (p, q) AP /\ In (p, q) (ablocks B ly1 S1) /\
  p <= a < p + req_size q /\ p + req_size q <= alloc_ceiling /\ ~ in_img SEGS a).
{ intros a Ha. destruct (HXB a Ha) as (p & q & Hin & Hpa). pose proof (INAP _ Hin) as Hab.
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p q HAR1 Hab) as (_ & _ & Hc & _).
  exists p, q. split; [exact Hin|]. split; [exact Hab|]. split; [exact Hpa|]. split; [exact Hc|].
  exact (proj2 (alx_client_img _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 a HAR1
    (or_introl (ex_intro _ p (ex_intro _ q (conj Hab Hpa)))))). }
assert (TNI : forall a, dxG cx <= a < dxG cx + 896 -> ~ in_img SEGS a).
{ intros a Ha. assert (Hb : dxG cx <= a < dxG cx + req_size ATABLE) by (change (req_size ATABLE) with 896; lia).
  exact (proj2 (alx_client_img _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 a HAR1
    (or_introl (ex_intro _ (dxG cx) (ex_intro _ ATABLE (conj GT Hb)))))). }
assert (GSI : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. destruct (df_pu_gs B RG HRGD a Ha) as (Hin & He). destruct (HG a Hin) as (Hi & Ho & _).
  split; [exact Hi|]. split; [exact Ho | exact He]. }
(* a byte of a block of Lr is off ddX *)
assert (NX : forall p q a, In (p, q) Lr -> p <= a < p + req_size q -> ~ ddX RG cx lo XB a).
{ intros p q a Hin Ha. assert (Hab : In (p, q) (ablocks B ly1 S1)) by (apply INL1; right; apply in_or_app; left; exact Hin).
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p q HAR1 Hab) as (_ & _ & Hc & _).
  pose proof (proj2 (alx_client_img _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 a HAR1
    (or_introl (ex_intro _ p (ex_intro _ q (conj Hab Ha)))))) as Hni.
  assert (HpG : p <> dxG cx).
  { intros E. apply NDG. rewrite map_app. apply in_or_app. left. rewrite <- E.
    exact (in_map fst Lr (p, q) Hin). }
  pose proof (NDL (p, q) Hin) as HpAP. cbn [fst] in HpAP.
  unfold ddX. intros [Hx | [Hx | [Hx | Hx]]].
  - apply Hni. apply (GSI a). unfold ASRC in *; lia.
  - apply (df_lp_rq_out_x B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p q (dxG cx) ATABLE a HAR1 Hab GT HpG Ha).
    change (req_size ATABLE) with 896. lia.
  - destruct (HXB' a Hx) as (p' & q' & Hin' & Hab' & Ha' & _).
    assert (Hne : p <> p') by (intros E; apply HpAP; rewrite E; exact (in_map fst AP (p', q') Hin')).
    exact (df_lp_rq_out_x B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p q p' q' a HAR1 Hab Hab' Hne Ha Ha').
  - lia. }
(* a byte of the table outside s->used, and an image byte outside g_s[j]'s 16..40, are off ddX *)
assert (NT : forall a, dxSA cx <= a < dxSA cx + 56 -> ~ (dxSA cx + 24 <= a < dxSA cx + 32) -> ~ ddX RG cx lo XB a).
{ intros a Ha Hn. pose proof (TNI a ltac:(lia)) as Hni.
  unfold ddX. intros [Hx | [Hx | [Hx | Hx]]].
  - apply Hni. apply (GSI a). unfold ASRC in *; lia.
  - exact (Hn Hx).
  - destruct (HXB' a Hx) as (p' & q' & Hin' & Hab' & Ha' & _).
    assert (Hne : dxG cx <> p').
    { intros E. apply NDG. rewrite map_app. apply in_or_app. right. rewrite E. exact (in_map fst AP (p', q') Hin'). }
    apply (df_lp_rq_out_x B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE p' q' a HAR1 GT Hab' Hne); [|exact Ha'].
    change (req_size ATABLE) with 896. lia.
  - lia. }
assert (NI : forall a, in_img SEGS a -> ~ (dHA RG cx + 16 <= a < dHA RG cx + 40) -> ~ ddX RG cx lo XB a).
{ intros a Hi Hn. pose proof (Hsegs a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  unfold ddX. intros [Hx | [Hx | [Hx | Hx]]].
  - exact (Hn Hx).
  - exact (TNI a ltac:(lia) Hi).
  - destruct (HXB' a Hx) as (_ & _ & _ & _ & _ & _ & Hni). exact (Hni Hi).
  - lia. }
(* the new block list *)
pose proof (dd_perm_drop (dxG cx, ATABLE) (hs_partial h1, APARTIAL) (aentry_blks e1)
  (if hl_cap (hs_pending h1) =? 0 then [] else [(hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1))])
  (map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) pre)
  (map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l2))
  (alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) (aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx)) as PD.
assert (EAP : AP = (if hl_cap (hs_pending h1) =? 0 then [] else [(hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1))]) ++
  map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) pre ++
  map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l2))
  by (unfold AP, alist_blks; rewrite Erecs, map_app; reflexivity).
rewrite <- EAP in PD. fold Lr in PD.
assert (EA2 : asrc_blks (dd_hset h1 l2 off2) = (hs_partial h1, APARTIAL) ::
  ((if hl_cap (hs_pending h1) =? 0 then [] else [(hl_v (hs_pending h1), AREC * hl_cap (hs_pending h1))]) ++
   map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l2)) ++
  alist_blks (hs_expected h1) ++ alist_blks (hs_held h1))
  by (unfold asrc_blks, dd_hset, alist_blks; cbn [hs_partial hs_pending hs_expected hs_held]; rewrite Ev, Ec; reflexivity).
rewrite <- EA2 in PD.
assert (HP2 : Permutation (ablocks B ly2 S2)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dd_hset h1 l2 off2) ++ aout_blks (drain_b_c.ds_ocap s) out ++
   dxrest cx)).
{ apply (Permutation_app_inv_l (map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) pre)).
  eapply Permutation_trans; [apply Permutation_sym; exact HPm|]. eapply Permutation_trans; [exact HP1|]. exact PD. }
assert (INL2 : forall b, In b ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks (dd_hset h1 l2 off2) ++
  aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) -> In b (ablocks B ly2 S2))
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HP2) Hb)).
assert (GT2 : In (dxG cx, ATABLE) (ablocks B ly2 S2)) by (apply INL2; left; reflexivity).
(* what is kept *)
assert (KBL : forall p q a, In (p, q) Lr -> p <= a < p + req_size q -> abyte_kept W1 m1 W2 m2 a).
{ intros p q a Hin Ha. assert (Hab : In (p, q) (ablocks B ly1 S1)) by (apply INL1; right; apply in_or_app; left; exact Hin).
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p q HAR1 Hab) as (_ & H4 & Hc & _).
  apply KX; [pose proof (@YM05.alloc_ceiling_lt rc) as ACL; lia | exact (NX p q a Hin Ha)
    | left; exists p, q; split; [exact Hab | exact Ha]]. }
assert (KF : forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha. apply KX; [lia | | right; right; exact Ha]. unfold ddX. intros [Hx | [Hx | [Hx | Hx]]].
  - unfold ASRC in *. lia.
  - lia.
  - destruct (HXB' a Hx) as (p' & q' & _ & _ & Ha' & Hc & _). lia.
  - lia. }
assert (KG : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= a < dHA RG cx + ASRC) ->
  abyte_kept W1 m1 W2 m2 a).
{ intros a Ha Hn. pose proof (proj1 (GSI a Ha)) as Hi. pose proof (Hsegs a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  destruct (GSI a Ha) as (_ & Ho & _).
  apply KX; [lia | apply NI; [exact Hi | unfold ASRC in *; lia]
    | right; left; split; [exact Hi | split; [exact Ho | exact (PSTG a Ha)]]]. }
assert (KO : akept W1 m1 W2 m2 (aout_fp B RG (drain_b_c.ds_ocap s) out)).
{ assert (CELL : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ Exists (in_zr a) PST ->
    ~ (rg_s RG <= a < rg_s RG + 4 * ASRC) -> abyte_kept W1 m1 W2 m2 a).
  { intros a Hi Ho Hq Hn. pose proof (Hsegs a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    apply KX; [lia | apply NI; [exact Hi | unfold ASRC in *; lia]
      | right; left; split; [exact Hi | split; [exact Ho | exact Hq]]]. }
  assert (PSL : forall a, inG (G_SL B RG) a -> ~ Exists (in_zr a) PST) by (intros a Ha; apply PSTO; left; exact Ha).
  assert (PGO : forall a, inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a ->
    ~ Exists (in_zr a) PST) by (intros a Ha; apply PSTO; right; exact Ha).
  intros r Hr a Ha. unfold aout_fp in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha;
    try (destruct (df_cell_facts B RG HGO HRGD a ltac:(lia)) as (_ & Hn & Hi & Ho & _);
         exact (CELL a Hi Ho (PGO a ltac:(ddx_inG)) Hn));
    try (destruct (df_pu_sl B RG HRGD a ltac:(lia)) as (Hin & _ & Hn);
         exact (CELL a (proj1 (HG a Hin)) (proj1 (proj2 (HG a Hin))) (PSL a ltac:(unfold G_SL; ddx_inG)) Hn));
    try (assert (HeG : inG (G_DR B RG) a)
           by (unfold G_DR, G_SL, inG; do 6 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia);
         destruct (df_errno_facts B RG HG HRGD a ltac:(lia)) as (_ & Hn & Hi);
         exact (CELL a Hi (proj1 (proj2 (HG a HeG))) (PSL a ltac:(unfold G_SL; ddx_inG)) Hn)).
  destruct (drain_b_c.ds_ocap s =? 0) eqn:Ec0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []].
  cbn [fst snd] in Ha.
  assert (Hin : In (out, drain_b_c.ds_ocap s) Lr).
  { unfold Lr. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. unfold aout_blks. rewrite Ec0.
    left. reflexivity. }
  apply Z.eqb_neq in Ec0.
  assert (Hab : In (out, drain_b_c.ds_ocap s) (ablocks B ly1 S1)) by (apply INL1; right; apply in_or_app; left; exact Hin).
  pose proof (BLKN ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 Hab) as Hn0'.
  pose proof (req_size_pos (drain_b_c.ds_ocap s) Hn0') as (_ & Hrq).
  apply (KBL out (drain_b_c.ds_ocap s) a Hin). lia. }
(* the new entry *)
assert (KSA : forall y, dxSA cx <= y < dxSA cx + 56 -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
  aview SEGS (w_H W2) m2 y = aview SEGS (w_H W1) m1 y).
{ intros y Hy Hn.
  assert (HyK : ddK_x ly1 S1 cx y)
    by (left; exists (dxG cx), ATABLE; split; [exact GT | change (req_size ATABLE) with 896; lia]).
  apply (proj1 (KX y ltac:(lia) (NT y Hy Hn) HyK)). }
assert (Hent2 : garr8 SEGS (arm W2 m2) (dxSA cx) (bzs (entry_bytes (dd_eadd e1 n)))).
{ unfold dd_eadd. apply (dd_entry_set B RG HGSB W1 W2 m1 m2 (dxSA cx) e1 (re_used e1 + n) Hgarr Hp1' Hp2' KSA Vu).
  pose proof HEOK as (_ & _ & _ & _ & _ & Hcr & HUl & _ & Hbj & _).
  destruct Hbj as [(Hc0 & _) | (_ & _ & Hjl & _)]; [lia|].
  destruct Hcr as [H | [H | H]]; lia. }
assert (Hawr2 : awr W2 m2 (dxSA cx) AENT).
{ intros i Hi. unfold AENT in Hi. replace (dxSA cx + i) with (dxG cx + (dxSA cx - dxG cx + i)) by lia.
  apply (df_blk_wr_x B ARx LAWS ly2 S2 Hp2 W2 m2 md2 (dxG cx) ATABLE HAR2 GT2). change (req_size ATABLE) with 896. lia. }
assert (Hokx2 : aentry_okx B ly2 S2 W2 m2 (dd_eadd e1 n)).
{ apply (dd_aentry_add B RG HGSB ly2 S2 W2 m2 e1 n); [| exact Hcp | exact Hn0 | exact Hnj].
  apply (df_aentry_okx_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 e1 HEOK).
  - apply (df_pu_aentry_kept B RG ly1 S1 W1 W2 m1 m2 e1 HEOK). intros p q a Hin Ha.
    apply (KBL p q a); [unfold Lr; apply in_or_app; left; exact Hin | exact Ha].
  - intros b Hb. apply INL2. right. apply in_or_app. left. exact Hb. }
(* the new source *)
assert (Hsrc2 : asrc_at B ly2 S2 W2 m2 (dHA RG cx) (dd_hset h1 l2 off2)).
{ apply (dd_asrc_set_x ly1 S1 Hp1 W1 m1 md1 ly2 S2 W2 m2 (dHA RG cx) h1 l2 off2 pre HAR1 Hsrc);
    [ | | | | exact HL2 | exact Ev | exact Ec | exact Erecs | exact Voff | exact Hoff].
  - intros a Ha Hn. pose proof (GSI a ltac:(unfold ASRC in *; lia)) as (Hi & Ho & _).
    pose proof (Hsegs a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    apply KX; [lia | exact (NI a Hi Hn)
      | right; left; split; [exact Hi | split; [exact Ho | apply PSTG; unfold ASRC in *; lia]]].
  - intros p q a Hin Ha. apply (KBL p q a); [|exact Ha].
    unfold Lr. apply in_or_app. right. apply in_or_app. left. exact Hin.
  - intros b Hb. apply INL2. right. apply in_or_app. right. apply in_or_app. left. rewrite EA2.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right. apply in_or_app. right. exact Hb.
  - pose proof Hsrc as (_ & _ & _ & _ & HAW1 & _). intros i Hi.
    destruct (GSI (dHA RG cx + i) ltac:(unfold ASRC in *; lia)) as (Hi' & Ho & He).
    apply (df_wr_img W1 W2 m1 m2 (dHA RG cx + i) Hi' (HPK2 _ Hi' Ho He) (HAW1 i Hi)). }
exact (dd_dmem_close_xR cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out ev sent LB ly2 S2 Hp2 W2 m2 md2 k2 (dd_eadd e1 n)
  (dd_hset h1 l2 off2) HM HJ2 Hrv2 HPK2 HFR2 KF Hent2 Hawr2 Hokx2 KG KO Hsrc2 HP2).
Qed.

Lemma dd_DMEM_s_xR : forall cx Hp ly S Hp1 (W : world SEGS) m md k e h s s' out ev sent LB,
drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
DMEM_xR B PST ARx RG R cx Hp ly S Hp1 W m md k e h s out ev sent LB ->
DMEM_xR B PST ARx RG R cx Hp ly S Hp1 W m md k e h s' out ev sent LB.
Proof. intros cx Hp ly S Hp1 W m md k e h s s' out ev sent LB H1 H2 H. unfold DMEM_xR in *. rewrite H1, H2. exact H. Qed.

Lemma dd_DJ_xR : forall cx Hp kr s1 D regs2 ly2 S2 Hp2 (W2 : world SEGS) m2 md2 k2 e1 h1 l2 off2 out1 ev1 LB1 spent2
  jb a o ha ks tl2,
dregs_line RG cx regs2 W2 m2 -> getr regs2 26 = w64 DR_SCAN_END -> getr regs2 24 = w64 (re_buf e1) ->
dinband (re_buf e1) (re_cap e1) ->
DMEM_xR B PST ARx RG R cx Hp ly2 S2 Hp2 W2 m2 md2 k2 (dd_eadd e1 (dnum s1)) (dd_hset h1 l2 off2) s1 out1 ev1
  (lines (dSTR cx) D) LB1 ->
bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 ->
DSAME cx e1 h1 ->
re_cap e1 = drain_b_c.ds_cap s1 -> bzs (re_U e1) = drain_b_c.ds_u s1 ->
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) ->
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 -> drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 ->
hs_eintr h1 = 0 ->
hs_state h1 = feed (drain_b_c.ds_ref s1) (ddata s1) ->
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) ->
hl_cap (hs_expected h1) = pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) ->
DHIST cx s1 D (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
RSTART cx s1 D ->
hl_v l2 = hl_v (hs_pending h1) -> hl_cap l2 = hl_cap (hs_pending h1) ->
map (fun r => bzs (snd r)) (hl_recs l2) = (if dwhole s1 then dtail s1 else drain_b_c.ds_pend s1) ->
off2 = (if dwhole s1 then 0 else drain_b_c.ds_off s1 + dnum s1) ->
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1) (drain_b_c.ds_H s1)
  (drain_b_c.ds_ka s1) (drl s1) jb o ha ks tl2 ->
dbud_x B MT RP MMAX cx kr ly2 S2 spent2 tl2 ->
DJ_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D 0 W2 (cfg_at SEGS (BASE + A_dr_join) regs2 m2 md2).
Proof.
intros cx Hp kr s1 D regs2 ly2 S2 Hp2 W2 m2 md2 k2 e1 h1 l2 off2 out1 ev1 LB1 spent2 jb a o ha ks tl2
  HRG R26 R24 HDB HM Hjunk HSAME Hcap HU Hsk HHk Hka Hei Hst Hen Hec HH HRS Ev Ec Erecs Eoff HFUT HBUD.
pose proof HRS as (Href & (_ & _ & _ & HNZ) & H4096 & Hdwf & _ & _ & Hpne).
pose proof Hdwf as (Hoff0 & Hoffl).
assert (HD : 0 <= dnum s1 /\ drain_b_c.ds_off s1 + dnum s1 <= Z.of_nat (length (dhead s1))).
{ unfold dnum, dhead, ulen in *. destruct (drain_b_c.ds_pend s1) as [|r rs] eqn:Ep; [congruence|].
  specialize (Hoffl r rs eq_refl). lia. }
destruct HD as (Hn0 & Hnl).
pose proof (dd_pstream s1 Hoff0 Hn0 Hnl) as HPS.
pose proof (dd_dwf_next s1 Hoff0 Hn0 Hnl) as HWN.
pose proof (dd_drl_len s1 HNZ) as HRL.
pose proof (dd_lines_len (ddata s1) (drain_b_c.ds_ref s1)) as HLL.
assert (HULEN : 0 <= ulen s1) by (unfold ulen; lia).
set (sv := dvirt cx s1 (dskp s1 0) (dlH cx s1 0) (dlka cx s1 0) (dlno s1 0) (dloc cx s1 0)).
assert (SNO : drain_b_c.ds_no sv = drain_b_c.ds_no s1) by (unfold sv, dvirt; cbn [drain_b_c.ds_no]; apply dd_dlno0).
assert (SOC : drain_b_c.ds_ocap sv = drain_b_c.ds_ocap s1) by reflexivity.
assert (SPS : pstream sv = prest (if dwhole s1 then dtail s1 else drain_b_c.ds_pend s1)
  (if dwhole s1 then 0 else drain_b_c.ds_off s1 + dnum s1)) by reflexivity.
exists regs2, ly2, S2, Hp2, m2, md2, k2, (dd_eadd e1 (dnum s1)), (dd_hset h1 l2 off2), out1, ev1, LB1, spent2,
  jb, a, o, ha, ks, tl2.
split; [reflexivity|].
split; [exact HRG|]. split; [exact R26|].
split; [unfold dd_eadd, drr_eset; cbn [re_buf]; rewrite Z.add_0_r; exact R24|].
split; [unfold dd_eadd, drr_eset; cbn [re_buf re_cap]; exact HDB|].
split; [unfold dd_eadd, drr_eset; cbn [re_cap]; lia|].
split; [unfold dbound; split; [lia | left; reflexivity]|].
split.
- unfold DLC_xR, LCORE_xR. fold sv. rewrite dd_drlp0, app_nil_r.
  split; [exact (dd_DMEM_s_xR cx Hp _ _ _ _ _ _ _ _ _ s1 sv _ _ _ _ SNO SOC HM)|].
  split.
  { unfold DLINK, dd_eadd, drr_eset, dd_hset, drain_b_c.ent_ka in *.
    cbn [re_cap re_U re_skip re_keys re_hp re_kh hs_eintr hs_pending hs_off hs_expected].
    unfold sv, dvirt, dnext. cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
      drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap].
    split; [exact Hcap|].
    split; [unfold bzs; rewrite map_app; fold (bzs (re_U e1)); fold (bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)));
      rewrite HU, Hjunk; reflexivity|].
    split; [exact Hsk|]. split; [exact HHk|]. split; [exact Hka|]. split; [rewrite Hei; reflexivity|].
    split; [exact Erecs|]. split; [exact Eoff|]. split; [exact Hst|].
    split; [exact Hen|]. split; [exact Hec|].
    unfold dwf. cbn [drain_b_c.ds_off drain_b_c.ds_pend]. exact HWN. }
  split.
  { unfold DSAME, dd_eadd, drr_eset, dd_hset in *.
    cbn [re_fd re_eof re_hp re_kh hs_fd hs_open hs_closed hs_pending hs_partial hs_held].
    rewrite Ev, Ec. exact HSAME. }
  split.
  { destruct HH as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
    unfold DHIST. unfold dd_hset. cbn [hs_expected].
    split; [rewrite P1, HPS, SPS, app_assoc; reflexivity|].
    split; [unfold sv, dvirt, dnext; cbn [drain_b_c.ds_ref]; rewrite P2, feed_app; reflexivity|].
    split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
    split; [rewrite SNO; exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
    split.
    - change (drain_b_c.ds_H sv) with (drain_b_c.ds_H s1). rewrite (dd_drlq0 s1 HNZ).
      rewrite HPS, length_app in P10. rewrite <- SPS in P10. lia.
    - assert (SEN : drain_b_c.ds_en sv = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1))) by reflexivity.
      rewrite SEN. unfold dref in *.
      rewrite HPS, length_app in P11. rewrite <- SPS in P11. lia. }
  split; [exact HRS | exact HBUD].
- rewrite dd_dlno0, (dd_drlq0 s1 HNZ).
  change (dloc cx s1 0) with (drain_b_c.ds_ocap s1). change (dlH cx s1 0) with (drain_b_c.ds_H s1).
  change (dlka cx s1 0) with (drain_b_c.ds_ka s1). exact HFUT.
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
Lemma dd_dmem_close_x : forall cx Hp ly S Hp1 W m md k e h s out ev sent LB ly' S' Hp1' W' m' md' k' e' h',
DMEM_x B PST ARx RG cx Hp ly S Hp1 W m md k e h s out ev sent LB ->
ajournal_gx_x SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly' S' Hp1' W' m' md' k' ->
rom_view SEGS W' m' -> apres_kept B W m W' m' -> frames S' = frames S ->
(forall a, dsp0 cx - DRAIN_FRAME <= a < dsp0 cx -> abyte_kept W m W' m' a) ->
garr8 SEGS (arm W' m') (dxSA cx) (bzs (entry_bytes e')) -> awr W' m' (dxSA cx) AENT ->
aentry_okx B ly' S' W' m' e' ->
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= a < dHA RG cx + ASRC) ->
   abyte_kept W m W' m' a) ->
akept W m W' m' (aout_fp B RG (drain_b_c.ds_ocap s) out) ->
asrc_at B ly' S' W' m' (dHA RG cx) h' ->
Permutation (ablocks B ly' S')
  ((dxG cx, ATABLE) :: aentry_blks e' ++ asrc_blks h' ++ aout_blks (drain_b_c.ds_ocap s) out ++ dxrest cx) ->
DMEM_x B PST ARx RG cx Hp ly' S' Hp1' W' m' md' k' e' h' s out ev sent LB.
Proof. eapply (dd_dmem_close_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Lemma dd_arm_close_x : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 s out ev sent LB
  ly2 S2 Hp2 (W2 : world SEGS) m2 md2 k2 lo XB l2 off2 pre n,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s out ev sent LB ->
ajournal_gx_x SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx)
  (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 k2 ->
rom_view SEGS W2 m2 -> apres_kept B W1 m1 W2 m2 -> frames S2 = frames S1 ->
alloc_ceiling <= lo ->
(forall a, XB a -> exists p q, In (p, q) (alist_blks (hs_pending h1)) /\ p <= a < p + req_size q) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ ddX RG cx lo XB a -> ddK_x ly1 S1 cx a -> abyte_kept W1 m1 W2 m2 a) ->
alist_at B ly2 S2 W2 m2 (dHA RG cx + 16) l2 false ->
hl_v l2 = hl_v (hs_pending h1) -> hl_cap l2 = hl_cap (hs_pending h1) ->
hl_recs (hs_pending h1) = pre ++ hl_recs l2 ->
Permutation (ablocks B ly1 S1)
  (map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) pre ++ ablocks B ly2 S2) ->
val_mem SEGS (arm W2 m2) (dHA RG cx + 32) 8 off2 ->
((hl_recs l2 = [] /\ off2 = 0) \/ (exists r rs, hl_recs l2 = r :: rs /\ 0 <= off2 < Z.of_nat (length (snd r)))) ->
val_mem SEGS (arm W2 m2) (dxSA cx + 24) 8 (re_used e1 + n) ->
0 <= n -> n <= Z.of_nat (length (re_junk e1)) -> 0 < re_cap e1 ->
DMEM_x B PST ARx RG cx Hp ly2 S2 Hp2 W2 m2 md2 k2 (dd_eadd e1 n) (dd_hset h1 l2 off2) s out ev sent LB.
Proof. eapply (dd_arm_close_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Lemma dd_DMEM_s_x : forall cx Hp ly S Hp1 (W : world SEGS) m md k e h s s' out ev sent LB,
drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
DMEM_x B PST ARx RG cx Hp ly S Hp1 W m md k e h s out ev sent LB ->
DMEM_x B PST ARx RG cx Hp ly S Hp1 W m md k e h s' out ev sent LB.
Proof. eapply (dd_DMEM_s_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Lemma dd_DJ_x : forall cx Hp kr s1 D regs2 ly2 S2 Hp2 (W2 : world SEGS) m2 md2 k2 e1 h1 l2 off2 out1 ev1 LB1 spent2
  jb a o ha ks tl2,
dregs_line RG cx regs2 W2 m2 -> getr regs2 26 = w64 DR_SCAN_END -> getr regs2 24 = w64 (re_buf e1) ->
dinband (re_buf e1) (re_cap e1) ->
DMEM_x B PST ARx RG cx Hp ly2 S2 Hp2 W2 m2 md2 k2 (dd_eadd e1 (dnum s1)) (dd_hset h1 l2 off2) s1 out1 ev1
  (lines (dSTR cx) D) LB1 ->
bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 ->
DSAME cx e1 h1 ->
re_cap e1 = drain_b_c.ds_cap s1 -> bzs (re_U e1) = drain_b_c.ds_u s1 ->
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) ->
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 -> drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 ->
hs_eintr h1 = 0 ->
hs_state h1 = feed (drain_b_c.ds_ref s1) (ddata s1) ->
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) ->
hl_cap (hs_expected h1) = pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) ->
DHIST cx s1 D (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
RSTART cx s1 D ->
hl_v l2 = hl_v (hs_pending h1) -> hl_cap l2 = hl_cap (hs_pending h1) ->
map (fun r => bzs (snd r)) (hl_recs l2) = (if dwhole s1 then dtail s1 else drain_b_c.ds_pend s1) ->
off2 = (if dwhole s1 then 0 else drain_b_c.ds_off s1 + dnum s1) ->
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1) (drain_b_c.ds_H s1)
  (drain_b_c.ds_ka s1) (drl s1) jb o ha ks tl2 ->
dbud_x B MT RP MMAX cx kr ly2 S2 spent2 tl2 ->
DJ_x B PST ARx MT RP MMAX RG cx Hp kr s1 D 0 W2 (cfg_at SEGS (BASE + A_dr_join) regs2 m2 md2).
Proof. eapply (dd_DJ_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
End cx.
End b.
End a.
