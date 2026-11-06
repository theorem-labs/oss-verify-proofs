(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B/W_drain_rest.v, the REST stage of the image-B (fuzz_reply.asan-ubsan) walk
   of fuzz_reply's drain.  Proves no function (kind: segment lemma): dr_rest : dr_rest_stmt B MT MMAX RG, the statement
   of lib/B/W_drain_cx.v (a working branch; that file is not edited).
   The walk, from fuzz_reply.asan-ubsan's objdump, from DLR 0x83e34 (no NUL in the buffer from p on):
     0x83e34  ld a0,232(sp); lbu a0,0(a0); bnez -> report     shadow check of s->used, NOT TAKEN
     0x83e40  sd s9,0(s6)                                     s->used = |W| - p
     0x83e44  mv a0,s3; mv a1,s8; mv a2,s9; jal __asan_memmove   memmove (buf, buf + p, |W| - p)   (AMEMMOVE)
     0x83e54  ld a0,0(s6); ld s8,208(sp); ld a1,184(sp)       a0 = s->used, s8 = SA + 8, a1 = 6001
     0x83e60  bltu a0,a1 -> 0x833c0                           the rest fits (relay.c LINE_LIMIT): DI
     0x83e64  ld a0,232(sp); lbu; bnez -> report; sd zero,0(s6)      else s->used = 0
     0x83e74  shadow check of s->skip (SA + 8), NOT TAKEN; li a0,1; sw a0,0(s8); j 0x833c0   s->skip = 1: DI
   No UBSan trap (W_drain_cx.v:182: "REST (0x83e34 .. 0x83e90) has no trap").  Both exits are DI 0x833c0 at the
   round state dnext (dlive cx) (dxmx cx) s1 and D ++ ddata s1: the model's chunk of the round leaves the rest
   skipn p (dW s1) when it is at most LINE_LIMIT bytes and drops it (skip set) otherwise (dr_chunk_rest below).
   STRUCTURE PORTED FROM a working branch 1c09e330abe lib/B/Prog/drain_p_rest_step.v (the two
   exits and their model) and lib/B/Prog/drain_p_rest_mm.v (the memmove of the rest); nothing is copied, the
   vocabulary (SRr over AR, journal ajournal_gx, symbolic seats) is this framework's.
   ARx form (an internal work row, the image-B twin of lib/A/W_drain_rest.v's Section cx): Section cx proves dr_rest_x,
   lib/B/W_drain_cx_x.v's dr_rest_stmt_x at the room texts, over any allocator relation ARx, its journal at
   W_contract_x.v's DRAIN_STK_x; the AR walk dr_rest (Section c) is unchanged. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx W_drain_dnrk W_drain_join.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
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


(* ------------------------------------------------------------------ the model: the rest of the buffer *)
Lemma dr_scan_nz : forall l skip acc, nozero l -> scan skip acc l = (skip, acc ++ l, []).
Proof.
induction l as [|b l IH]; intros skip acc Hz; [rewrite app_nil_r; reflexivity|].
inversion Hz as [|b' l' Hb Hl]; subst. rewrite (scan_nz skip acc b l Hb), (IH skip (acc ++ [b]) Hl), <- app_assoc.
reflexivity.
Qed.

Lemma dr_scan_app : forall l1 l2 skip acc,
scan skip acc (l1 ++ l2) =
let '(sk1, r1, ls1) := scan skip acc l1 in let '(sk2, r2, ls2) := scan sk1 r1 l2 in (sk2, r2, ls1 ++ ls2).
Proof.
induction l1 as [|b l1 IH]; intros l2 skip acc.
- cbn [app scan]. destruct (scan skip acc l2) as [[sk2 r2] ls2]. reflexivity.
- cbn [app scan]. destruct (Z.eqb b 0).
  + rewrite IH. destruct (scan false [] l1) as [[sk1 r1] ls1]. destruct (scan sk1 r1 l2) as [[sk2 r2] ls2].
    destruct (skip || Nat.ltb LINE_LIMIT (length acc)); reflexivity.
  + apply IH.
Qed.

Lemma dr_nozero_skipn : forall (l : list Z) p, (forall i, (p <= i)%nat -> nth_error l i <> Some 0) -> nozero (skipn p l).
Proof.
intros l p H. unfold nozero. apply Forall_forall. intros b Hb E. subst b.
apply In_nth_error in Hb as (i & Hi). rewrite nth_error_skipn in Hi. exact (H (p + i)%nat ltac:(lia) Hi).
Qed.

(* the round's chunk when the bytes from p on hold no NUL and p starts a line *)
Lemma dr_chunk_rest : forall s1 p, dbound s1 p -> nozero (drain_b_c.ds_u s1) ->
(forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0) ->
drlq s1 p = [] /\
dchunk s1 = (if Nat.ltb LINE_LIMIT (length (dW s1) - p) then [] else skipn p (dW s1),
             if Nat.ltb LINE_LIMIT (length (dW s1) - p) then true else dskp s1 p, drlp s1 p).
Proof.
intros s1 p (Hpl & Hp) Hu Hnz.
pose proof (dr_nozero_skipn (dW s1) p Hnz) as Hz.
assert (HQ : scan (dskp s1 p) [] (skipn p (dW s1)) = (dskp s1 p, skipn p (dW s1), [])) by exact (dr_scan_nz _ _ [] Hz).
assert (HP : scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1)) = (dskp s1 p, [], drlp s1 p)).
{ unfold drlp, dskp. destruct (Nat.eq_dec p 0) as [-> | Hp0]; [reflexivity|].
  destruct Hp as [-> | Hz1]; [lia|].
  - rewrite (proj2 (Nat.eqb_neq p 0) Hp0).
    assert (HF : firstn p (dW s1) = firstn (p - 1) (dW s1) ++ [0]).
    { rewrite <- (firstn_skipn (p - 1) (firstn p (dW s1))). rewrite firstn_firstn. replace (Nat.min (p - 1) p) with (p - 1)%nat by lia.
      f_equal. rewrite skipn_firstn_comm. replace (p - (p - 1))%nat with 1%nat by lia.
      destruct (skipn (p - 1) (dW s1)) as [|b r] eqn:Es.
      - exfalso. assert (Hlt : (p - 1 < length (dW s1))%nat) by (apply nth_error_Some; rewrite Hz1; discriminate).
        assert (HL0 : length (skipn (p - 1) (dW s1)) = 0%nat) by (rewrite Es; reflexivity).
        rewrite length_skipn in HL0. lia.
      - cbn. replace (p - 1)%nat with (p - 1 + 0)%nat in Hz1 by lia. rewrite <- nth_error_skipn in Hz1.
        rewrite Es in Hz1. cbn in Hz1. injection Hz1 as ->. reflexivity. }
    rewrite HF, dr_scan_app.
    destruct (scan (drain_b_c.ds_skip s1) [] (firstn (p - 1) (dW s1))) as [[sk1 r1] ls1].
    cbn. reflexivity. }
split.
- unfold drlq. rewrite HQ. reflexivity.
- unfold dchunk, chunk.
  assert (HS : scan (drain_b_c.ds_skip s1) (drain_b_c.ds_u s1) (ddata s1) = (dskp s1 p, skipn p (dW s1), drlp s1 p)).
  { pose proof (dr_scan_app (drain_b_c.ds_u s1) (ddata s1) (drain_b_c.ds_skip s1) []) as E.
    rewrite (dr_scan_nz _ _ [] Hu) in E. cbn [app] in E.
    destruct (scan (drain_b_c.ds_skip s1) (drain_b_c.ds_u s1) (ddata s1)) as [[sk2 r2] ls2] eqn:E2.
    fold (dW s1) in E. rewrite <- (firstn_skipn p (dW s1)), dr_scan_app, HP, HQ in E.
    rewrite app_nil_r in E. injection E as -> -> ->. reflexivity. }
  rewrite HS. rewrite length_skipn. destruct (Nat.ltb LINE_LIMIT (length (dW s1) - p)); reflexivity.
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

(* ------------------------------------------------------------------ the round state REST hands to DI *)
Lemma drr_next_model : forall cx s1 D p, RSTART cx s1 D -> dbound s1 p ->
(forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0) ->
drlq s1 p = [] /\
drain_b_c.ds_cap (dnext (dlive cx) (dxmx cx) s1) = drain_b_c.ds_cap s1 /\
drain_b_c.ds_u (dnext (dlive cx) (dxmx cx) s1) =
  (if Nat.ltb LINE_LIMIT (length (dW s1) - p) then [] else skipn p (dW s1)) /\
drain_b_c.ds_skip (dnext (dlive cx) (dxmx cx) s1) =
  (if Nat.ltb LINE_LIMIT (length (dW s1) - p) then true else dskp s1 p) /\
drain_b_c.ds_H (dnext (dlive cx) (dxmx cx) s1) = dlH cx s1 p /\
drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1) = dlka cx s1 p /\
drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) = dlno s1 p /\
drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) = dloc cx s1 p /\
drain_b_c.ds_eintr (dnext (dlive cx) (dxmx cx) s1) = false /\
lines (dSTR cx) (D ++ ddata s1) = lines (dSTR cx) D ++ drlp s1 p /\
J1 (drain_b_c.ds_u (dnext (dlive cx) (dxmx cx) s1)) (drain_b_c.ds_skip (dnext (dlive cx) (dxmx cx) s1))
   (drain_b_c.ds_ref (dnext (dlive cx) (dxmx cx) s1)).
Proof.
intros cx s1 D p HRS Hbnd Hnz. pose proof HRS as (Href & HJ1 & _).
pose proof HJ1 as (_ & _ & _ & Hu0).
destruct (dr_chunk_rest s1 p Hbnd Hu0 Hnz) as [HQ HCK].
pose proof (chunk_ok _ _ _ (ddata s1) HJ1) as CK.
change (chunk (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (ddata s1)) with (dchunk s1) in CK.
rewrite HCK in CK. cbv beta iota in CK. destruct CK as [CK1 CK2].
split; [exact HQ|].
unfold dnext, drl, dlH, dlka, dlno, dloc, dlrun. rewrite HCK.
cbn [fst snd drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_no
  drain_b_c.ds_ocap drain_b_c.ds_eintr drain_b_c.ds_ref].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [rewrite lines_app, <- Href, CK1; reflexivity | exact CK2].
Qed.

Lemma drr_DMEM_s : forall (B : asyms) (RG : rep_globals) cx ly S (W : world SEGS) m md k e h s s' out ev sent LB,
drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
DMEM B RG cx ly S W m md k e h s out ev sent LB -> DMEM B RG cx ly S W m md k e h s' out ev sent LB.
Proof. intros B RG cx ly S W m md k e h s s' out ev sent LB H1 H2 H. unfold DMEM in *. rewrite H1, H2. exact H. Qed.

Lemma drr_DHIST : forall cx s s' D F sent kl h LB nk,
pstream s' = pstream s -> drain_b_c.ds_ref s' = drain_b_c.ds_ref s -> drain_b_c.ds_no s' = drain_b_c.ds_no s ->
drain_b_c.ds_H s' = drain_b_c.ds_H s -> drain_b_c.ds_en s' = drain_b_c.ds_en s ->
DHIST cx s D F sent kl h LB nk -> DHIST cx s' D F sent kl h LB nk.
Proof.
intros cx s s' D F sent kl h LB nk H1 H2 H3 H4 H5 H. unfold DHIST in *. rewrite H1, H2, H3, H4, H5. exact H.
Qed.

Lemma drr_DLINK : forall s s' e e' h, DLINK s e h ->
re_cap e' = drain_b_c.ds_cap s' -> bzs (re_U e') = drain_b_c.ds_u s' ->
re_skip e' = (if drain_b_c.ds_skip s' then 1 else 0) ->
drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H s' -> drain_b_c.ent_ka e' = drain_b_c.ds_ka s' ->
drain_b_c.ds_eintr s' = drain_b_c.ds_eintr s -> drain_b_c.ds_pend s' = drain_b_c.ds_pend s ->
drain_b_c.ds_off s' = drain_b_c.ds_off s -> drain_b_c.ds_ref s' = drain_b_c.ds_ref s ->
drain_b_c.ds_en s' = drain_b_c.ds_en s -> drain_b_c.ds_ecap s' = drain_b_c.ds_ecap s ->
DLINK s' e' h.
Proof.
intros s s' e e' h (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12) H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
unfold DLINK. rewrite H6, H7, H8, H9, H10, H11.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact L6|]. split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|].
split; [exact L11|]. unfold dwf in *. rewrite H8, H7. exact L12.
Qed.

(* ------------------------------------------------------------------ the symbolic state at 0x83e34 *)
(* Atoms 0..31: the registers, with s6 = SA + 24 pinned; 32 = SA, 33 = SHADOW_OFF.  The frame region holds the slots the
   walk reads (184: 6001, 208: SA + 8, 232: shadow (SA + 24), 240: SHADOW_OFF); the entry's two stored fields are two
   regions with their own write windows: s->skip [8, 12) and s->used [24, 32). *)
Definition drr_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 352 0 0
    [YP09.mkChunk 184 (CVal 8 (SLit 6001)); YP09.mkChunk 208 (CVal 8 (SOff 32 8)); YP09.mkChunk 232 (dj_shg 24);
     YP09.mkChunk 240 (CVal 8 (SOff 33 0))].
Definition drr_e1 : YP09.region := YP09.mkRegion (Some 32%nat) 0 16 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 34 0))].
Definition drr_e3 : YP09.region := YP09.mkRegion (Some 32%nat) 24 32 24 32 [].
Definition drr_regs : list sv := sr_set sr_atoms 22%bv (SOff 32 24).
Definition drr_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, dj_PTRF); (24%nat, mkAF 4096 140737479966720 0);
            (25%nat, mkAF 0 16384 0); (32%nat, dj_PTRF); (33%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (34%nat, mkAF 0 1 0) ] [] [].
Definition drr_ss : sstate := mkSS A_dr_rest drr_regs [drr_frame; drr_e1; drr_e3] None drr_facts.
Definition drr_extra (SA sk : Z) : list word := map (Z_to_bv 64) [SA; SHADOW_OFF; sk].

(* ------------------------------------------------------------------ bytes and the entry *)
Lemma drr_nth_skipn : forall (A : Type) (l : list A) i j d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
intros A l i j d. revert l. induction j as [|j IH]; intros l; [reflexivity|].
destruct l as [|b l]; [destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma drr_garr8_view : forall H (m : word -> option byte) base l,
(forall j, (j < length l)%nat -> aview SEGS H m (base + Z.of_nat j) = Some (nth j l 0)) ->
garr8 SEGS (mrestrict H m) base l.
Proof.
intros H m base l Hv j Hj. destruct (aview_byte SEGS H m _ _ (Hv j Hj)) as (b & Hb & Hbv & Hr). split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite (Z.mod_small (nth j l 0) 256 Hr). rewrite (Z.mod_small (nth j l 0) 256 Hr).
rewrite Hbv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the buffer after the move-down: [0, n) holds the old [p, p + n), the rest is as it was *)
Lemma drr_buf_moved : forall H (m : word -> option byte) buf (U J : list byte) p n,
Z.of_nat p + n = Z.of_nat (length U) -> 0 <= n ->
(forall i, 0 <= i < n -> aview SEGS H m (buf + i) = Some (nth (p + Z.to_nat i) (bzs (U ++ J)) 0)) ->
(forall i, n <= i < Z.of_nat (length (U ++ J)) -> aview SEGS H m (buf + i) = Some (nth (Z.to_nat i) (bzs (U ++ J)) 0)) ->
garr8 SEGS (mrestrict H m) buf (bzs (skipn p U ++ skipn (Z.to_nat n) (U ++ J))).
Proof.
intros H m buf U J p n Hpn Hn H1 H2. apply drr_garr8_view. intros j Hj.
unfold bzs in Hj |- *. rewrite map_app, length_app, !length_map, !length_skipn, length_app in Hj.
rewrite map_app.
assert (LS : length (map bz (skipn p U)) = Z.to_nat n) by (rewrite length_map, length_skipn; lia).
destruct (Nat.lt_ge_cases j (Z.to_nat n)) as [Hlt | Hge].
- rewrite app_nth1 by lia. rewrite <- skipn_map, drr_nth_skipn.
  replace (buf + Z.of_nat j) with (buf + Z.of_nat j) by reflexivity.
  rewrite (H1 (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id. unfold bzs. rewrite map_app, app_nth1; [reflexivity|].
  rewrite length_map. lia.
- rewrite app_nth2 by lia. rewrite LS, <- skipn_map, drr_nth_skipn.
  rewrite (H2 (Z.of_nat j) ltac:(rewrite length_app; lia)). rewrite Nat2Z.id. unfold bzs.
  f_equal. f_equal. lia.
Qed.

(* the source_t at SA with its skip and used fields rewritten *)
Definition drr_eset (e : rentry) (sk u : Z) (U J : list byte) : rentry :=
RE (re_fd e) (re_eof e) sk (re_pad1 e) (re_buf e) u (re_cap e) (re_hp e) (re_kh e) (re_pad2 e) (re_keys e) U J.

Lemma drr_entry_set : forall H (m m' : word -> option byte) SA e sk u U J,
garr8 SEGS (mrestrict H m) SA (bzs (entry_bytes e)) -> length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
(forall y, SA <= y < SA + 56 -> ~ (SA + 8 <= y < SA + 12) -> ~ (SA + 24 <= y < SA + 32) ->
   aview SEGS H m' y = aview SEGS H m y) ->
val_mem SEGS (mrestrict H m') (SA + 8) 4 sk -> val_mem SEGS (mrestrict H m') (SA + 24) 8 u ->
0 <= sk < 2 ^ 32 -> 0 <= u < 2 ^ 64 ->
garr8 SEGS (mrestrict H m') SA (bzs (entry_bytes (drr_eset e sk u U J))).
Proof.
intros H m m' SA e sk u U J Hg Hp1 Hp2 KM Vs Vu Hsk Hu.
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
assert (KEEP : forall a l, garr8 SEGS (mrestrict H m) a l -> SA <= a -> a + Z.of_nat (length l) <= SA + 56 ->
  (a + Z.of_nat (length l) <= SA + 8 \/ SA + 12 <= a) -> (a + Z.of_nat (length l) <= SA + 24 \/ SA + 32 <= a) ->
  garr8 SEGS (mrestrict H m') a l).
{ intros a l Hl H1 H2 H3 H4. apply (garr8_frame SEGS _ _ a l Hl). intros x Hx.
  apply (mbyte_of_aview SEGS). apply KM; lia. }
rewrite dnk_entry_split. unfold drr_eset.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys].
change (re_nheld (RE (re_fd e) (re_eof e) sk (re_pad1 e) (re_buf e) u (re_cap e) (re_hp e) (re_kh e) (re_pad2 e)
  (re_keys e) U J)) with (re_nheld e).
apply (proj2 (garr8_app SEGS _ _ _ _)). split; [apply KEEP; [exact G1 | lia | rewrite L44; lia | rewrite L44; lia | rewrite L44; lia]|].
rewrite L44.
apply (proj2 (garr8_app SEGS _ _ _ _)).
split; [rewrite (dnk_le4_bytes sk ltac:(lia)); apply dnk_le_garr8; [exact Vs | cbn; lia]|].
rewrite L4. replace (SA + 8 + 4) with (SA + 12) by lia.
apply (proj2 (garr8_app SEGS _ _ _ _)). split; [apply KEEP; [exact G3 | lia | rewrite LP; lia | rewrite LP; lia | rewrite LP; lia]|].
rewrite LP. replace (SA + 12 + 4) with (SA + 16) by lia.
apply (proj2 (garr8_app SEGS _ _ _ _)). split; [apply KEEP; [exact G4 | lia | rewrite L8; lia | rewrite L8; lia | rewrite L8; lia]|].
rewrite L8. replace (SA + 16 + 8) with (SA + 24) by lia.
apply (proj2 (garr8_app SEGS _ _ _ _)).
split; [rewrite (dnk_le8_bytes u ltac:(lia)); apply dnk_le_garr8; [exact Vu | cbn; lia]|].
rewrite L8. replace (SA + 24 + 8) with (SA + 32) by lia.
apply KEEP; [exact G6 | lia | rewrite LT; lia | rewrite LT; lia | rewrite LT; lia].
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

Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

Lemma drr_seat : forall (W1 : world SEGS) regs1 m1 sp SA buf x n sk,
spZ regs1 = sp -> 2 ^ 46 <= sp -> alloc_ceiling <= sp -> sp + 352 <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 22 = w64 (SA + 24) -> getr regs1 19 = w64 buf -> getr regs1 24 = w64 x -> getr regs1 25 = w64 n ->
val_mem SEGS (arm W1 m1) (sp + 184) 8 6001 -> val_mem SEGS (arm W1 m1) (sp + 208) 8 (SA + 8) ->
val_mem SEGS (arm W1 m1) (sp + 232) 8 (shadow_addr (SA + 24)) -> val_mem SEGS (arm W1 m1) (sp + 240) 8 SHADOW_OFF ->
awr W1 m1 SA AENT -> val_mem SEGS (arm W1 m1) (SA + 8) 4 sk -> 0 <= sk <= 1 ->
4096 <= SA -> SA + 56 <= alloc_ceiling -> SA mod 8 = 0 ->
4096 <= buf <= 140737479966720 -> buf mod 8 = 0 -> 0 <= n <= 16384 -> 4096 <= x <= 140737479966720 ->
range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF SA 56 ->
(forall y, SA <= y < SA + 56 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (drr_extra SA sk))) drr_ss
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_rest)) m1 (seg_rom SEGS))) /\
sh_ok SEGS dj_Bx dj_SH (Eimg (Ereg regs1 (drr_extra SA sk))) (mrestrict (w_H W1) m1).
Proof.
intros W1 regs1 m1 sp SA buf x n sk Hsp Hs1 Hs0 Hs2 Hs16 R22 R19 R24 R25 F184 F208 F232 F240 HAW V8 Hsk HSA1 HSA2 HSA8
  Hb1 Hb8 Hn Hx RA HAPP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (drr_extra SA sk))).
assert (EREG : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by (intros nn r Hnn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ nn r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (U19 : bv_unsigned (ew E 19) = buf)
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite R19; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = x)
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); rewrite R24; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = n)
  by (rewrite (EREG 25%nat 25%bv) by (first [lia | reflexivity]); rewrite R25; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = SHADOW_OFF) by (rewrite E33; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E34 : ew E 34 = Z_to_bv 64 sk) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (U34 : bv_unsigned (ew E 34) = sk) by (rewrite E34; apply unsigned_lit_small; lia).
split.
- apply pa_entry_st_ok_full.
  + unfold drr_regs. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    rewrite R22. rewrite (den_atom E 32 SA 24 E32) by lia. reflexivity.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * unfold region_ok, drr_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ sp 184 8 (SLit 6001) 6001);
           [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact F184].
      -- apply (chunk_ok_val SEGS E _ sp 208 8 (SOff 32 8) (SA + 8));
           [exact (den_atom E 32 SA 8 E32 ltac:(lia) ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
           | zside | exact F208].
      -- apply (chunk_ok_val SEGS E _ sp 232 8 _ (shadow_addr (SA + 24)));
           [exact (dj_den_sh E SA 24 E32 E33 ltac:(lia) ltac:(lia) ltac:(lia)) | | zside | exact F232].
         change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold shadow_addr, SHADOW_OFF.
         split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | ].
         assert ((SA + 24) / 8 <= SA + 24) by (apply Z.div_le_upper_bound; lia). lia.
      -- apply (chunk_ok_val SEGS E _ sp 240 8 (SOff 33 0) SHADOW_OFF);
           [exact (den_atom0 E 33 SHADOW_OFF E33 ltac:(unfold SHADOW_OFF; lia))
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | zside | exact F240].
    * unfold region_ok, drr_e1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (HAW o); unfold AENT; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ SA 8 4 (SOff 34 0) sk);
        [exact (den_atom0 E 34 sk E34 ltac:(lia)) | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | zside | exact V8].
    * unfold region_ok, drr_e3. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (HAW o). unfold AENT. lia.
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, drr_frame, drr_e1, drr_e3.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U32.
    split; [split; [right; lia | split; [right; lia | exact I]] | split; [split; [left; lia | exact I] | split; exact I]].
  + split; [|split; [exact I | exact I]].
    unfold drr_facts, dj_PTRF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U19, U24, U25, U32, U33, U34.
    assert (M16 : sp mod 2 ^ 4 = 0) by (change (2 ^ 4) with 16; exact Hs16).
    assert (M8a : SA mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact HSA8).
    assert (M8b : buf mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact Hb8).
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; try reflexivity;
      unfold SHADOW_OFF in *; lia.
- unfold sh_ok, dj_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E dj_Bx 32 SA 56 SA 0 56 RA).
  + unfold dj_Bx. apply (U_atom E 33 SHADOW_OFF E33). unfold SHADOW_OFF; lia.
  + apply (U_atom E 32 SA E32). lia.
  + lia.
  + lia.
  + intros y Hy. change (Z.min 0 56) with 0 in Hy. change (Z.max 0 56) with 56 in Hy. apply HAPP. lia.
Qed.

(* ------------------------------------------------------------------ the entry and DMEM after the move-down *)
Definition drr_eblks_rest (e : rentry) : list (Z * Z) :=
(if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]) ++
map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e).

(* lib/B/W_drain_topb_bk.v:641-689 dtk_aentry_junk (a working branch c0a3958f203),
   with the used bytes, the skip flag and the junk all replaced and the held keys' bytes kept *)
Lemma drr_aentry_move : forall ly S (W : world SEGS) m m' e sk u U J,
aentry_okx B ly S W m e -> 0 < re_cap e ->
(sk = 0 \/ sk = 1) -> Z.of_nat (length U) = u -> u <= re_cap e -> Z.of_nat (length J) = re_cap e - u ->
garr8 SEGS (arm W m') (re_buf e) (bzs (U ++ J)) ->
(forall p n x, In (p, n) (drr_eblks_rest e) -> p <= x < p + n -> abyte_kept W m W m' x) ->
aentry_okx B ly S W m' (drr_eset e sk u U J).
Proof.
intros ly S W m m' e sk u U J HE Hcp Hsk HU Huc HJ HGb KB.
unfold aentry_okx in HE |- *. unfold drr_eset.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
destruct HE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
split; [exact H1|]. split; [exact Hsk|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split; [exact HU|]. split; [exact Huc|].
split.
{ destruct H9 as [(Hc & _) | (Hc & Hin & _)]; [lia | right].
  split; [exact Hc|]. split; [exact Hin|]. split; [exact HJ | exact HGb]. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11 | right].
  split; [exact Hz|]. split; [exact Hin|]. split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (KB (re_hp e) (re_kh e)).
  - unfold drr_eblks_rest. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  - unfold bzs in Hx. rewrite length_map, (dnk_key_ptrs_len B RG) in Hx. unfold re_nheld in Hk1. lia. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [exact K1|]. split; [|exact K3].
apply (akept_garr8 W m); [|exact K2].
intros x Hx. apply (KB (key_addr k) (Z.of_nat (length (key_text k)) + 1)).
- unfold drr_eblks_rest. apply in_or_app. right.
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
- unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

(* DMEM after REST's writes: the moved buffer, s->skip and s->used, and a call's scratch below drain's frame *)
Lemma drr_DMEM_move : forall cx ly1 S1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 lo sk u U J,
DBASE B MT MMAX RG cx ->
DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k2 ->
alloc_ceiling <= lo -> 0 < re_cap e1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (re_buf e1 <= a < re_buf e1 + re_cap e1) -> ~ (dxSA cx + 8 <= a < dxSA cx + 12) ->
  ~ (dxSA cx + 24 <= a < dxSA cx + 32) -> ~ (lo <= a < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
val_mem SEGS (arm W1 m2) (dxSA cx + 8) 4 sk -> val_mem SEGS (arm W1 m2) (dxSA cx + 24) 8 u ->
(sk = 0 \/ sk = 1) -> 0 <= u -> Z.of_nat (length U) = u -> u <= re_cap e1 ->
Z.of_nat (length J) = re_cap e1 - u -> garr8 SEGS (arm W1 m2) (re_buf e1) (bzs (U ++ J)) ->
DMEM B RG cx ly1 S1 W1 m2 md2 k2 (drr_eset e1 sk u U J) h1 sg out1 ev1 sent LB1.
Proof.
intros cx ly1 S1 W1 m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 lo sk u U J HB HMEM HJ2 Hlo Hcp KM HP Vs Vu
  Hsk Hu0 HUl Huc HJl HGB.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
pose proof HB as (Hafn & _ & _ & HSAlo & HSAhi & _ & _ & _ & _ & Hj & _).
change AENT with 56 in HSAhi. change ATABLE with 896 in HSAhi.
pose proof Hafn as (_ & _ & _ & _ & _ & (_ & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hslo, Hshi.
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
pose proof asan_consts as (C1 & _).
assert (GT : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR GT) as (_ & HG4 & HGc & _).
change (req_size ATABLE) with 896 in HGc.
pose proof HEOK as (_ & _ & Hp1 & Hp2 & _ & _ & _ & _ & Hbufc & _).
destruct Hbufc as [(Hc0 & _) | (_ & HBin & _)]; [lia|].
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR HBin) as (_ & HB4 & HBc & _).
pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq).
pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 _ _ HAR GT) as Hoff. red in Hoff. change (req_size ATABLE) with 896 in Hoff.
pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 _ _ HAR HBin) as HBoff. red in HBoff.
assert (Ec0 : (re_cap e1 =? 0) = false) by (apply Z.eqb_neq; lia).
set (L2 := (dxG cx, ATABLE) :: drr_eblks_rest e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx).
assert (HP2 : Permutation (ablocks B ly1 S1) ((re_buf e1, re_cap e1) :: L2)).
{ eapply Permutation_trans; [exact Hperm|]. unfold L2, aentry_blks, drr_eblks_rest. rewrite Ec0. cbn [app].
  apply perm_swap. }
assert (HSEP : dxG cx + 896 <= re_buf e1 \/ re_buf e1 + req_size (re_cap e1) <= dxG cx).
{ assert (HP3 : Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: (re_buf e1, re_cap e1) ::
    (drr_eblks_rest e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)))
    by (eapply Permutation_trans; [exact Hperm|]; unfold aentry_blks, drr_eblks_rest; rewrite Ec0; cbn [app];
        apply Permutation_refl).
  pose proof (sep_blocks_perm SEGS B LAWS ly1 S1 W1 m1 md1 _ _ _ HAR HP3) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. exact Hd. }
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (re_buf e1 <= a < re_buf e1 + req_size (re_cap e1)) ->
  ~ (dxG cx <= a < dxG cx + 896) -> ~ (lo <= a < dsp0 cx - DRAIN_FRAME) -> abyte_kept W1 m1 W1 m2 a).
{ intros a Ha H1 H2 H3. split; [apply KM; lia|]. unfold arm. apply (writable_kept (w_H W1) m1 m2 a (HP a)). }
assert (HKX : forall a, dnk_low cx a -> dnx_low (re_buf e1, re_cap e1) a -> abyte_kept W1 m1 W1 m2 a).
{ intros a (Ha & Ht) (_ & Hb). cbn [fst snd] in Hb. apply HK; [lia | exact Hb | change ATABLE with 896 in Ht; exact Ht | lia]. }
assert (HKF : forall a, dsp0 cx - DRAIN_FRAME <= a < 2 ^ 64 -> abyte_kept W1 m1 W1 m2 a)
  by (intros a Ha; apply HK; lia).
assert (HKI : forall a, 0x10000 <= a < 0x5fc000 -> abyte_kept W1 m1 W1 m2 a) by (intros a Ha; apply HK; lia).
assert (HVMF : forall a v, dsp0 cx - DRAIN_FRAME <= a -> a + 8 <= dsp0 cx ->
  val_mem SEGS (arm W1 m1) a 8 v -> val_mem SEGS (arm W1 m2) a 8 v).
{ intros a v H1 H2 Hv. apply (akept_vm W1 m1); [|exact Hv]. intros x Hx. apply HKF. lia. }
pose proof HGSB as (GS1 & GS2 & GS3). unfold IMG_TOP, ASRC in GS2.
assert (HVMG : forall a v, rg_s RG <= a -> a + 4 <= rg_s RG + 4 * ASRC ->
  val_mem SEGS (arm W1 m1) a 4 v -> val_mem SEGS (arm W1 m2) a 4 v).
{ intros a v H1 H2 Hv. apply (akept_vm W1 m1); [|exact Hv]. intros x Hx. cbn in Hx. apply HKI. unfold ASRC in *. lia. }
assert (HBIN : forall b, In b (aentry_blks e1) \/ In b (asrc_blks h1) \/ In b (aout_blks (drain_b_c.ds_ocap sg) out1) ->
  In b (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)).
{ intros b [Hb | [Hb | Hb]]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb |].
  right; apply in_or_app; right; apply in_or_app; left; exact Hb. }
assert (HBIN2 : forall b, In b (asrc_blks h1) \/ In b (aout_blks (drain_b_c.ds_ocap sg) out1) -> In b L2).
{ intros b [Hb | Hb]; unfold L2; right; apply in_or_app; right; apply in_or_app;
    [left; exact Hb | right; apply in_or_app; left; exact Hb]. }
split; [exact HJ2|].
split.
{ intros a Ha. pose proof Ha as (sg0 & Hsg & _ & Hr).
  pose proof (pa_img_range a (ex_intro _ sg0 (conj Hsg Hr))) as Hai.
  rewrite (proj1 (HKI a Hai)). exact (Hrom a Ha). }
split; [intros a Ha1 Ha2 Ha3 Ha4; apply HP; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  repeat match type of HFR with _ /\ _ => let A := fresh "A" in destruct HFR as [A HFR] end.
  repeat match goal with |- _ /\ _ => split end;
    first [ apply HVMF; [lia | lia | assumption]
          | intros i Hi; apply HVMF; [unfold DR_SAVE_OFF; lia | unfold DR_SAVE_OFF; lia | exact (HFR i Hi)] ]. }
split.
{ apply (drr_entry_set (w_H W1) m1 m2 (dxSA cx) e1 sk u U J Hgarr Hp1 Hp2); [| exact Vs | exact Vu | lia | lia].
  intros y Hy Hy1 Hy2. apply KM; lia. }
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split.
{ apply (drr_aentry_move ly1 S1 W1 m1 m2 e1 sk u U J HEOK Hcp Hsk HUl Huc HJl HGB).
  intros pb nb x Hin Hx.
  assert (Hin1 : In (pb, nb) (aentry_blks e1))
    by (unfold aentry_blks; rewrite Ec0; right; exact Hin).
  assert (HinL2 : In (pb, nb) L2) by (unfold L2; right; apply in_or_app; left; exact Hin).
  assert (Hab : In (pb, nb) (ablocks B ly1 S1)) by (apply (Permutation_in _ (Permutation_sym HP2)); right; exact HinL2).
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 pb nb HAR Hab) as (_ & _ & _ & _ & _ & _ & Hnb).
  pose proof (req_size_pos nb ltac:(lia)) as (_ & Hrqb).
  apply HKX.
  - exact (proj1 (dnk_low_blk B RG LAWS HG HGSB cx ly1 S1 W1 m1 md1 _ pb nb x HAR Hperm
      ltac:(apply in_or_app; left; exact Hin1) ltac:(lia))).
  - exact (proj1 (dnx_low_blk B RG LAWS HG HGSB (re_buf e1, re_cap e1) ly1 S1 W1 m1 md1 L2 pb nb x HAR HP2 HinL2 ltac:(lia))). }
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc);
    [|exact (dnk_asrc_blks_in B RG HGSB ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc)].
  intros r Hr a Ha. apply HKX.
  - exact (proj1 (dnk_fp_src B RG LAWS HG HRGD HGSB HSD HSM cx ly1 S1 W1 m1 md1 _ h1 HAR Hperm
      (fun b Hb => HBIN b (or_intror (or_introl Hb))) GT Hj Hsrc r Hr a Ha)).
  - exact (proj1 (dnx_fp_src B RG LAWS HG HRGD HGSB HSD HSM (re_buf e1, re_cap e1) cx ly1 S1 W1 m1 md1 L2 h1 HAR HP2
      (fun b Hb => HBIN2 b (or_introl Hb)) HBin Hj Hsrc r Hr a Ha)). }
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis). exists f, o.
  assert (Hi4 : Z.of_nat i < 4) by lia. unfold ASRC in *.
  split; [apply HVMG; [lia | lia | exact V1]|].
  split; [apply HVMG; [lia | lia | exact V2] | exact Hdis]. }
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  pose proof (HKI x ltac:(unfold ASRC in *; lia)) as (Hk1 & Hk2).
  split; [rewrite Hk1; exact Hv|]. intros Hwr. exact (Hk2 (Hw Hwr)). }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout| |].
  - intros r Hr a Ha. apply HKX.
    + exact (proj1 (dnk_fp_out B MMAX RG LAWS HG HRGD HGSB HMMAX HV9 HSD HSM cx ly1 S1 W1 m1 md1 _ _ _ _ _ _ _ HAR Hperm
        (fun b Hb => HBIN b (or_intror (or_intror Hb))) Hout r Hr a Ha)).
    + exact (dnx_fp_out B RG LAWS HG HGSB HV9 HSD HSM (re_buf e1, re_cap e1) ly1 S1 W1 m1 md1 _ _ _ _ _ _ L2 HAR HP2
        (fun b Hb => HBIN2 b (or_intror Hb)) Hout r Hr a Ha).
  - exact (dnk_aout_blks_in B RG HGSB ly1 S1 W1 m1 _ _ _ _ _ _ Hout). }
split; [exact Hlivout | exact Hperm].
Qed.

(* the relay's buffer, a block of the round's entry: a write to it is one the journal allows (awr_byte's FP or
   temporary-block case).  It is one of the entry's blocks at drain's entry (then in dFP), or new in the round. *)
Lemma drr_buf_awr : forall cx ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 a,
DBASE B MT MMAX RG cx -> DMEM B RG cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
(re_cap e1 = 8192 \/ re_cap e1 = 16384) -> In (re_buf e1, re_cap e1) (ablocks B ly1 S1) ->
re_buf e1 <= a < re_buf e1 + re_cap e1 ->
(inFP (dFP cx) a /\ exists b nb, In (b, nb) (ablocks B ly1 S1) /\ b <= a < b + req_size nb) \/
in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 a HB HM Hcap HBin Ha.
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq).
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y})
  by (intros [x1 x2] [y1 y2]; destruct (Z.eq_dec x1 y1), (Z.eq_dec x2 y2);
      [left; congruence | right; congruence | right; congruence | right; congruence]).
destruct (in_dec Hdec (re_buf e1, re_cap e1) (ablocks B (dxly cx) (dxS cx))) as [Hin0 | Hnin0].
- left. split; [|exists (re_buf e1), (re_cap e1); split; [exact HBin | lia]].
  apply (Permutation_in _ Hperm0) in Hin0. destruct Hin0 as [Heq | Hin0].
  + injection Heq as _ Hc. unfold ATABLE in Hc. lia.
  + apply in_app_or in Hin0 as [Hin0 | Hin0].
    * exists (re_buf e1, re_buf e1 + req_size (re_cap e1)). split; [|cbn [fst snd]; lia].
      unfold dFP, dr_fp. right. unfold ablocks_fp. apply (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ (re_buf e1, re_cap e1)).
      apply in_or_app. left. exact Hin0.
    * apply in_app_or in Hin0 as [Hin0 | Hin0].
      -- exists (re_buf e1, re_buf e1 + req_size (re_cap e1)). split; [|cbn [fst snd]; lia].
         unfold dFP, dr_fp. right. unfold ablocks_fp. apply (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ (re_buf e1, re_cap e1)).
         apply in_or_app. right. apply in_or_app. left. exact Hin0.
      -- apply in_app_or in Hin0 as [Hin0 | Hin0].
         ++ exists (re_buf e1, re_buf e1 + req_size (re_cap e1)). split; [|cbn [fst snd]; lia].
            unfold dFP, dr_fp. right. unfold ablocks_fp. apply (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ (re_buf e1, re_cap e1)).
            apply in_or_app. right. apply in_or_app. right. exact Hin0.
         ++ (* the buffer is in the rest of the blocks too: twice in the round's blocks, impossible *)
            exfalso. destruct (in_split _ _ Hin0) as (r1 & r2 & Er).
            assert (Ec0 : (re_cap e1 =? 0) = false) by (apply Z.eqb_neq; lia).
            assert (HP2 : Permutation (ablocks B ly1 S1)
              ((re_buf e1, re_cap e1) :: (re_buf e1, re_cap e1) :: (dxG cx, ATABLE) ::
               ((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
                map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
               asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ r1 ++ r2)).
            { eapply Permutation_trans; [exact Hperm|].
              unfold aentry_blks. rewrite Ec0, Er. cbn [app].
              eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
              eapply Permutation_trans; [apply perm_skip | apply perm_swap].
              rewrite !app_assoc. apply Permutation_sym, Permutation_middle. }
            pose proof (sep_blocks_perm SEGS B LAWS ly1 S1 W1 m1 md1 _ _ _ HAR HP2) as Hd.
            unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
- right. exists (re_buf e1), (re_cap e1). split; [exact HBin|]. split; [exact Hnin0 | lia].
Qed.

Theorem dr_rest : dr_rest_stmt B MT MMAX RG.
Proof.
unfold dr_rest_stmt. intros cx s1 D p W1 c1 HB HDLR Kdi.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDLR as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl &
  Hc1 & HRG & R26 & R24 & R25 & R19 & HDB & HCAP & Hbnd & Hnz & HDLC & HFUT).
subst c1.
pose proof HRG as (Hsp & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & HFR).
pose proof HDLC as HLC. unfold DLC, LCORE in HLC.
destruct HLC as (HM & HL & HSAME & HH & HRS & HBUD).
pose proof HM as (HJ & Hrom & _ & _ & _ & Hgarr & Hawr & HEOK & _ & _ & _ & _ & _ & Hperm).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
pose proof HB as (Hafn & _ & HGB & HSAlo & HSAhi & HSA8 & _ & _ & _ & Hj & _).
change AENT with 56 in HSAhi. change ATABLE with 896 in HSAhi.
pose proof Hafn as (_ & _ & _ & Hgp & Htp & (Hal16 & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK = 16880) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR GT) as (HG16 & HG4 & HGc & HGapp & _).
change (req_size ATABLE) with 896 in HGc, HGapp.
pose proof HEOK as (Heof & Hskp & Hp1 & Hp2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & _).
destruct Hbufc as [(Hc0 & _) | (Hcpos & HBin & Hjunk & Hbgarr)]; [lia|].
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR HBin) as (HB16 & HB4 & HBc & HBapp & HBpres & _).
pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq).
pose proof HL as (_ & HU & _).
cbn [dvirt drain_b_c.ds_u] in HU.
assert (HUL : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HU; unfold bzs; rewrite length_map; exact HUlen).
assert (Hcap16 : re_cap e1 <= 16384) by (destruct Hcapr as [H|[H|H]]; lia).
pose proof HDB as (Hdb1 & Hdb2 & Hdb3). unfold DCEIL in Hdb2.
pose proof Hbnd as (Hpl & _).
pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F184 & _ & F208 & _ & _ & F232 & F240 & _).
pose proof (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx) 56 HAR GT
  HSAlo ltac:(change (req_size ATABLE) with 896; lia)) as RA.
assert (HAPP : forall y, dxSA cx <= y < dxSA cx + 56 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)).
{ intros y Hy. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
destruct (drr_seat W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_buf e1) (re_buf e1 + Z.of_nat p)
  (Z.of_nat (length (dW s1) - p)) (re_skip e1)
  Hsp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; rewrite HDF; reflexivity)
  R22 R19 R24 R25 F184 F208 F232 F240 Hawr
  (dnk_entry_skip (arm W1 m1) (dxSA cx) e1 Hgarr Hp1 ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia) HSA8
  ltac:(lia) Hdb3 ltac:(lia) ltac:(lia) RA HAPP) as [HS SHOK].
remember (Eimg (Ereg regs1 (drr_extra (dxSA cx) (re_skip e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by (intros nn r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ nn r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_skip e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
clear HE.
assert (B2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (B32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (FPE : forall y, dxSA cx <= y < dxSA cx + 56 ->
  inFP (dFP cx) y /\ exists b nb, In (b, nb) (ablocks B ly1 S1) /\ b <= y < b + req_size nb).
{ intros y Hy. split.
  - exists (dxSA cx, dxSA cx + AENT). split; [unfold dFP, dr_fp; left; reflexivity | cbn [fst snd]; unfold AENT; lia].
  - exists (dxG cx), ATABLE. split; [exact GT | change (req_size ATABLE) with 896; lia]. }
unfold cfg_at. change (w64 (BASE + A_dr_rest)) with (Z_to_bv 64 (BASE + A_dr_rest)).
paj_run_tok RUN HS HJ SHOK dj_Bspan.
{ lazymatch goal with |- awr_ok_x ?E0 ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x E0 rs' G XO OUT stk sp0 fp b0 bc ly own) end.
  repeat first [ apply awr_ok_x_nil
    | apply awr_ok_x_cons; [ intros y Hy; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy; rewrite ?B2, ?B32 in Hy;
        first [ lia | left; split; [right; left; apply FPE; lia | lia] ] | ] ]. }
lazymatch type of HS with context [restrict _ ?y] => rename y into msC end.
rename HFr into FR1; rename HG0 into GR1; clear HF.
assert (HSEP : dxG cx + 896 <= re_buf e1 \/ re_buf e1 + req_size (re_cap e1) <= dxG cx).
{ assert (Ec0 : (re_cap e1 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (HP2 : Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: (re_buf e1, re_cap e1) ::
    (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
      map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
     asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p)
       (dloc cx s1 p))) out1 ++ dxrest cx))).
  { eapply Permutation_trans; [exact Hperm|]. unfold aentry_blks. rewrite Ec0. cbn [app]. apply Permutation_refl. }
  pose proof (sep_blocks_perm SEGS B LAWS ly1 S1 W1 m1 md1 _ _ _ HAR HP2) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. exact Hd. }
(* the first run wrote only s->used *)
assert (KL1 : forall y, 0 <= y < 2 ^ 64 -> ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
  aview SEGS (w_H W1) (ms_mem msC) y = aview SEGS (w_H W1) m1 y).
{ intros y Hy Hy1 Hy2; apply (aview_eq_of SEGS); apply FR1; rewrite unsigned_lit_small by lia;
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2, ?B32 in Hr; lia |]); destruct Hin. }
assert (KP1 : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msC) y)
  by (intros y Hy; exact (apresent_grows _ _ _ _ GR1 Hy)).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARC.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Usp0 : spZ (ms_regs msC) = dsp0 cx - DRAIN_FRAME).
{ unfold spZ at 1. rewrite Q2, (EREG 2%nat 2%bv) by (first [lia | reflexivity]). exact Hsp. }
set (n := Z.of_nat (length (dW s1) - p)) in *.
assert (Hnp : Z.of_nat p + n = re_used e1) by (unfold n; rewrite Nat2Z.inj_sub by lia; lia).
assert (Hn0 : 0 <= n) by (unfold n; lia).
assert (HUJ : Z.of_nat (length (bzs (re_U e1 ++ re_junk e1))) = re_cap e1)
  by (unfold bzs; rewrite length_map, length_app; lia).
(* the buffer's bytes, as the reader sees them at the call *)
assert (BYTEC : forall j, (j < length (bzs (re_U e1 ++ re_junk e1)))%nat ->
  aview SEGS (w_H W1) (ms_mem msC) (re_buf e1 + Z.of_nat j) = Some (nth j (bzs (re_U e1 ++ re_junk e1)) 0)).
{ intros j Hjl. rewrite KL1 by (unfold AENT, ATABLE in *; lia).
  rewrite <- (app_nil_r (bzs (re_U e1 ++ re_junk e1))) in Hbgarr.
  pose proof (dj_buf_byte (w_H W1) m1 (re_buf e1) (bzs (re_U e1 ++ re_junk e1)) [] j Hbgarr Hjl) as R.
  exact R. }
assert (HVIS : forall y, re_buf e1 <= y < re_buf e1 + re_cap e1 -> exists v, aview SEGS (w_H W1) (ms_mem msC) y = Some v).
{ intros y Hy. replace y with (re_buf e1 + Z.of_nat (Z.to_nat (y - re_buf e1))) by lia.
  rewrite BYTEC by lia. eexists; reflexivity. }
assert (HNIMG : forall y, re_buf e1 <= y < re_buf e1 + re_cap e1 -> ~ in_img SEGS y)
  by (intros y Hy; exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 _ _ y HAR HBin ltac:(lia))).
pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 _ _ HAR GT) as Hoff. red in Hoff. change (req_size ATABLE) with 896 in Hoff.
assert (Hromc : rom_view SEGS W1 (ms_mem msC)).
{ intros y Hy. pose proof Hy as (sg0 & Hsg & _ & Hr). pose proof (pa_img_range y (ex_intro _ sg0 (conj Hsg Hr))) as Hyi.
  rewrite KL1 by lia. exact (Hrom y Hy). }
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 [] ESTACK (SIGMA WS_asan_memmove)
    (fun y => re_buf e1 <= y < re_buf e1 + n)
    (fun regs' mem' => getr regs' 10 = w64 (re_buf e1) /\
       forall i, 0 <= i < n -> aview SEGS (w_H W1) mem' (re_buf e1 + i) =
         aview SEGS (w_H W1) (ms_mem msC) (re_buf e1 + Z.of_nat p + i))
    W1 (ms_regs msC) (ms_mem msC) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) []
    ly1 S1 _ k1 (-352) (Z_to_bv 64 (BASE + 6928))).
  - exact HG.
  - reflexivity.
  - exact HJ.
  - rewrite Usp0, HDF. lia.
  - reflexivity.
  - lia.
  - lia.
  - rewrite HDS. unfold ESTACK; lia.
  - rewrite Q3, (EREG 3%nat 3%bv) by (first [lia | reflexivity]). rewrite R3. exact Hgp.
  - rewrite Q4, (EREG 4%nat 4%bv) by (first [lia | reflexivity]). rewrite R4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros y. destruct (Z_lt_le_dec y (re_buf e1)); [right; lia|].
    destruct (Z_lt_le_dec y (re_buf e1 + n)); [left; lia | right; lia].
  - intros y Hy HGy. exfalso. exact (HNIMG y ltac:(lia) (proj1 (HG y HGy))).
  - intros y Hy _. split; [|lia].
    destruct (drr_buf_awr cx ly1 S1 W1 m1 md1 k1 e1 h1 _ out1 ev1 _ LB1 y HB HM
      ltac:(destruct Hcapr as [H|[H|H]]; lia) HBin ltac:(lia)) as [Ha | Ha];
      [right; left; exact Ha | right; right; left; exact Ha].
  - intros HPRE2 _.
    apply (AMEMMOVE ly1 S1 W1 (ms_regs msC) (ms_mem msC) _ (re_buf e1) (re_buf e1 + Z.of_nat p) n HPRE2).
    + rewrite Q10, (EREG 19%nat 19%bv) by (first [lia | reflexivity]). exact R19.
    + rewrite Q11, (EREG 24%nat 24%bv) by (first [lia | reflexivity]). exact R24.
    + rewrite Q12, (EREG 25%nat 25%bv) by (first [lia | reflexivity]). exact R25.
    + lia.
    + lia.
    + lia.
    + intros y Hy. split; [|split].
      * destruct (HVIS y ltac:(lia)) as (v & Hv).
        exact (dnk_writable_view (w_H W1) (ms_mem msC) y v ltac:(lia) Hv
          (fun Hr => HNIMG y ltac:(lia) (let '(ex_intro _ sg0 (conj Hsg (conj _ Hrr))) := Hr in
             ex_intro _ sg0 (conj Hsg Hrr)))).
      * exact (proj2 (HBpres y ltac:(lia))).
      * rewrite Usp0. unfold ESTACK. lia.
    + unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
    + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1) _ n HARC HBin);
        lia.
    + intros Hpos.
      apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1) _ n HARC HBin);
        lia.
    + lia.
    + lia.
    + intros y Hy. split; [destruct (HVIS y ltac:(lia)) as (v & Hv); rewrite Hv; discriminate|].
      rewrite Usp0. unfold ESTACK. lia.
    + unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
    + apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1) _ n HARC HBin);
        lia.
    + intros Hpos.
      apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1) _ n HARC HBin);
        lia.
    + exact Hromc.
    + intros Hpos. pose proof (@ASAN_CEIL_range rc) as (Hcc & _). pose proof HBapp as (Ha0 & HLH).
      split; destruct HLH as [HLo | [HH1 HH2]];
        unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; [left; lia | right; lia | left; lia | right; lia].
    + intros y Hy. exact (HNIMG y ltac:(lia)). }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HR10 & HMV) & Hfr2 & Hpres2).
assert (FR2 : forall y, 0 <= y < 2 ^ 64 -> ~ (re_buf e1 <= y < re_buf e1 + n) ->
  ~ (dsp0 cx + -352 - ESTACK <= y < dsp0 cx + -352) -> aview SEGS (w_H W1) mem2 y = aview SEGS (w_H W1) (ms_mem msC) y)
  by exact Hfr2.
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 2%nat (dsp0 cx - DRAIN_FRAME));
      [exact B2 | intros y Hy; apply FR2; [lia | lia | unfold ESTACK; lia] | exact Hpres2].
  - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 32%nat (dxSA cx));
      [exact B32 | intros y Hy; apply FR2; [lia | lia | unfold ESTACK; lia] | exact Hpres2].
  - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 32%nat (dxSA cx));
      [exact B32 | intros y Hy; apply FR2; [lia | lia | unfold ESTACK; lia] | exact Hpres2]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (E32a : ew Ea 32 = Z_to_bv 64 (dxSA cx)) by (rewrite OLDa by lia; exact E32).
assert (E33a : ew Ea 33 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDa by lia; exact E33).
assert (B2a : bv_unsigned (ew Ea 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDa by lia; exact B2).
assert (B32a : bv_unsigned (ew Ea 32) = dxSA cx) by (rewrite OLDa by lia; exact B32).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (SHOK2 : sh_ok SEGS dj_Bx dj_SH Ea (mrestrict (w_H W1) mem2)).
{ unfold sh_ok, dj_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) mem2 Ea dj_Bx 32 (dxSA cx) 56 (dxSA cx) 0 56
    (range_addressable_of_block SEGS B LAWS ly1 S1 W1 mem2 md2 (dxG cx) ATABLE (dxSA cx) 56 HAR2 GT
      HSAlo ltac:(change (req_size ATABLE) with 896; lia))).
  + unfold dj_Bx. apply (U_atom Ea 33 SHADOW_OFF E33a). unfold SHADOW_OFF; lia.
  + apply (U_atom Ea 32 (dxSA cx) E32a). lia.
  + lia.
  + lia.
  + intros y Hy. change (Z.min 0 56) with 0 in Hy. change (Z.max 0 56) with 56 in Hy. apply HAPP. lia. }
paj_run_tok RUN HS HJ2 SHOK2 dj_Bspan.
{ lazymatch goal with |- awr_ok_x ?E0 ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x E0 rs' G XO OUT stk sp0 fp b0 bc ly own) end.
  repeat first [ apply awr_ok_x_nil
    | apply awr_ok_x_cons; [ intros y Hy; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy; rewrite ?B2a, ?B32a in Hy;
        first [ lia | left; split; [right; left; apply FPE; lia | lia] ] | ] ]. }
lazymatch type of HS with context [restrict _ ?y] => rename y into msD end.
rename HFr into FR3; rename HG0 into GR3; clear HF.
assert (KL3 : forall y, 0 <= y < 2 ^ 64 -> ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
  aview SEGS (w_H W1) (ms_mem msD) y = aview SEGS (w_H W1) mem2 y).
{ intros y Hy Hy1 Hy2; apply (aview_eq_of SEGS); apply FR3; rewrite unsigned_lit_small by lia;
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2a, ?B32a in Hr; lia |]); destruct Hin. }
assert (KPD : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msD) y)
  by (intros y Hy; exact (apresent_grows _ _ _ _ GR3 (Hpres2 y (KP1 y Hy)))).
assert (KMD : forall y, 0 <= y < 2 ^ 64 -> ~ (re_buf e1 <= y < re_buf e1 + re_cap e1) ->
  ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
  ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) (ms_mem msD) y = aview SEGS (w_H W1) m1 y).
{ intros y Hy H1 H2 H3 H4. rewrite KL3 by assumption. rewrite FR2 by (unfold ESTACK in *; lia). apply KL1; assumption. }
assert (HBUFD : garr8 SEGS (arm W1 (ms_mem msD)) (re_buf e1)
  (bzs (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)))).
{ apply (drr_buf_moved (w_H W1) (ms_mem msD) (re_buf e1) (re_U e1) (re_junk e1) p n); [lia | lia | |].
  - intros i Hi. rewrite KL3 by lia. rewrite (HMV i Hi).
    replace (re_buf e1 + Z.of_nat p + i) with (re_buf e1 + Z.of_nat (p + Z.to_nat i)) by lia.
    apply BYTEC. unfold bzs. rewrite length_map, length_app. lia.
  - intros i Hi. rewrite length_app in Hi. rewrite KL3 by lia. rewrite FR2 by (unfold ESTACK in *; lia).
    replace (re_buf e1 + i) with (re_buf e1 + Z.of_nat (Z.to_nat i)) by lia.
    apply BYTEC. unfold bzs. rewrite length_map, length_app. lia. }
assert (HLBUF : Z.of_nat (length (bzs (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)))) = re_cap e1).
{ unfold bzs. rewrite length_map, length_app, !length_skipn, length_app. lia. }
destruct (drr_next_model cx s1 D p HRS Hbnd Hnz) as (HQ & NCAP & NU & NSK & NH & NKA & NNO & NOC & NEI & HSENT & NJ1).
unfold dlfut in HFUT. rewrite HQ in HFUT. cbv zeta in HFUT. cbn [drain_b_c.lines_run fst snd] in HFUT.
destruct HFUT as (tl2 & HLAT & Htl). cbn [app] in Htl. rewrite <- Htl in HLAT.
rewrite HQ in HH. cbn [length] in HH. change (Z.of_nat 0) with 0 in HH. rewrite <- HSENT in HH.
assert (E34a : ew Ea 34 = Z_to_bv 64 (re_skip e1)) by (rewrite OLDa by lia; exact E34).
assert (KEPT : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew Ea nn = getr regs1 r)
  by (intros nn r Hn Hr; rewrite OLDa by lia; exact (EREG nn r Hn Hr)).
assert (E25a : ew Ea 25 = Z_to_bv 64 n)
  by (rewrite (KEPT 25%nat 25%bv) by (first [lia | reflexivity]); exact R25).
psrr_branch_tok RUN BR HS SHOK2 dj_Bspan.
- (* the rest fits (used < 6001): s->used = |W| - p, DI *)
  assert (Hn6 : n < 6001).
  { rewrite W_traps.trap_br_ltu in Hc. rewrite (U_atom Ea 25 n E25a) in Hc by lia. rewrite (U_lit Ea 6001) in Hc by lia.
    apply Z.ltb_lt in Hc. exact Hc. }
  clear Hc.
  assert (HBIG : Nat.ltb LINE_LIMIT (length (dW s1) - p) = false).
  { apply Nat.ltb_ge. apply Nat2Z.inj_le. change (Z.of_nat LINE_LIMIT) with 6000.
    assert (Hz : Z.of_nat (length (dW s1) - p) < 6001) by exact Hn6. lia. }
  rewrite HBIG in NU, NSK.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 dj_Bspan A_dr_top.
  { lazymatch goal with |- awr_ok_x ?E0 ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok_x E0 rs' G XO OUT stk sp0 fp b0 bc ly own) end.
    repeat first [ apply awr_ok_x_nil
      | apply awr_ok_x_cons; [ intros y Hy; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy; rewrite ?B2a, ?B32a in Hy;
          first [ lia | left; split; [right; left; apply FPE; lia | lia] ] | ] ]. }
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR4; rename HG0 into GR4; clear HF.
  assert (KL4 : forall y, 0 <= y < 2 ^ 64 -> ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) (ms_mem msD) y).
  { intros y Hy Hy1 Hy2; apply (aview_eq_of SEGS); apply FR4; rewrite unsigned_lit_small by lia;
    intros (r & Hin & Hr); vm_compute in Hin;
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2a, ?B32a in Hr; lia |]); destruct Hin. }
  assert (KPF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR4 (KPD y Hy))).
  assert (KMF : forall y, 0 <= y < 2 ^ 64 -> ~ (re_buf e1 <= y < re_buf e1 + re_cap e1) ->
    ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y)
    by (intros y Hy H1 H2 H3 H4; rewrite KL4 by assumption; apply KMD; assumption).
  assert (HBUFF : garr8 SEGS (arm W1 (ms_mem msF)) (re_buf e1)
    (bzs (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)))).
  { apply (dnk_garr8_kept W1 (ms_mem msD) W1 (ms_mem msF) _ _ HBUFD). intros x Hx. rewrite HLBUF in Hx.
    apply KL4; lia. }
  lazymatch type of HS with
  | st_ok _ ?Ev ?ss _ => pose proof (st_ok_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_region_nth Ev ss _ 2 _ HS eq_refl) as RG2
  | st_ok_pi _ _ ?Ev ?ss _ => pose proof (st_ok_pi_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_pi_region_nth Ev ss _ 2 _ HS eq_refl) as RG2
  end.
  cbn [ms_mem restrict] in RG1, RG2.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 8 4 _ (re_skip e1) RG1 B32a ltac:(cbn [In]; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E34a; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)) as Vs.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 24 8 _ n RG2 B32a ltac:(cbn [In]; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E25a; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as Vu.
  pose proof (drr_DMEM_move cx ly1 S1 W1 m1 (ms_mem msF) md1 _ k1 _ e1 h1 _ out1 ev1 _ LB1
    (dsp0 cx - DRAIN_FRAME - ESTACK) (re_skip e1) n (skipn p (re_U e1)) (skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)) HB HM HJ2 ltac:(unfold ESTACK; lia) ltac:(lia) KMF KPF Vs Vu
    ltac:(lia) ltac:(lia) (ltac:(rewrite length_skipn; lia) : Z.of_nat (length (skipn p (re_U e1))) = n)
    ltac:(lia) (ltac:(rewrite length_skipn, length_app; lia) : Z.of_nat (length (skipn (Z.to_nat n) (re_U e1 ++ re_junk e1))) = re_cap e1 - n) HBUFF) as HMF.
  pose proof (drr_DMEM_s B RG cx _ _ _ _ _ _ _ h1
    (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p)) (dnext (dlive cx) (dxmx cx) s1) out1 ev1 _ LB1
    ltac:(rewrite NNO; reflexivity) ltac:(rewrite NOC; reflexivity) HMF) as HMF2.
  rewrite <- HSENT in HMF2.
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  apply Kdi.
  exists (ms_regs msF), ly1, S1, (ms_mem msF). eexists. eexists.
  exists (drr_eset e1 (re_skip e1) n (skipn p (re_U e1)) (skipn (Z.to_nat n) (re_U e1 ++ re_junk e1))), h1, out1, ev1, LB1, spent. eexists. eexists. exists tl.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (KEPT 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite X3, (KEPT 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite X4, (KEPT 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite X21, (KEPT 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
    split; [rewrite X24, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X20, (KEPT 20%nat 20%bv) by (first [lia | reflexivity]); exact R20|].
    split; [rewrite X22, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, (KEPT 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|].
    split; [rewrite X8, (KEPT 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|].
    split; [rewrite X9, (KEPT 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
    split; [rewrite X18, (KEPT 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
    rewrite X26, (KEPT 26%nat 26%bv) by (first [lia | reflexivity]); exact R26. }
  split; [exact HMF2|].
  split.
  { unfold drr_eset. cbn [re_U]. intros Hin. apply (in_map bz) in Hin.
    replace (bz (Z_to_bv 8 0)) with 0 in Hin by reflexivity. rewrite <- skipn_map in Hin. fold (bzs (re_U e1)) in Hin.
    rewrite HU in Hin. apply In_nth_error in Hin as (i & Hi). rewrite nth_error_skipn in Hi.
    exact (Hnz (p + i)%nat ltac:(lia) Hi). }
  split; [unfold drr_eset; cbn [re_used]; unfold APARTIAL; lia|].
  split; [intros _; exact HDB|].
  split.
  { apply (drr_DLINK _ _ e1 _ h1 HL).
    * unfold drr_eset. cbn [re_cap]. rewrite NCAP. pose proof HL as (L1 & _). cbn [dvirt drain_b_c.ds_cap] in L1. exact L1.
    * unfold drr_eset. cbn [re_U]. rewrite NU. unfold bzs. rewrite <- skipn_map. fold (bzs (re_U e1)). rewrite HU. reflexivity.
    * unfold drr_eset. cbn [re_skip]. rewrite NSK. pose proof HL as (_ & _ & L3 & _). cbn [dvirt drain_b_c.ds_skip] in L3. exact L3.
    * unfold drr_eset. cbn [re_keys]. rewrite NH. pose proof HL as (_ & _ & _ & L4 & _). cbn [dvirt drain_b_c.ds_H] in L4. exact L4.
    * unfold drr_eset, drain_b_c.ent_ka. cbn [re_hp re_kh]. rewrite NKA. pose proof HL as (_ & _ & _ & _ & L5 & _).
      cbn [dvirt drain_b_c.ds_ka] in L5. unfold drain_b_c.ent_ka in L5. exact L5.
    * rewrite NEI. reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity. }
  split; [exact HSAME|].
  split.
  { apply (drr_DHIST cx (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))
      (dnext (dlive cx) (dxmx cx) s1) _ _ _ _ h1 LB1 0 eq_refl eq_refl ltac:(rewrite NNO; reflexivity)
      ltac:(rewrite NH; reflexivity) eq_refl HH). }
  split; [exact NJ1|].
  split; [exact HLAT | exact HBUD].
- (* the rest is over LINE_LIMIT: s->used = 0, s->skip = 1, DI *)
  assert (Hn6 : 6001 <= n).
  { rewrite W_traps.trap_br_ltu in Hc. rewrite (U_atom Ea 25 n E25a) in Hc by lia. rewrite (U_lit Ea 6001) in Hc by lia.
    apply Z.ltb_ge in Hc. exact Hc. }
  clear Hc.
  assert (HBIG : Nat.ltb LINE_LIMIT (length (dW s1) - p) = true).
  { apply Nat.ltb_lt. apply Nat2Z.inj_lt. change (Z.of_nat LINE_LIMIT) with 6000.
    assert (Hz : 6001 <= Z.of_nat (length (dW s1) - p)) by exact Hn6. lia. }
  rewrite HBIG in NU, NSK.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 dj_Bspan A_dr_top.
  { lazymatch goal with |- awr_ok_x ?E0 ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok_x E0 rs' G XO OUT stk sp0 fp b0 bc ly own) end.
    repeat first [ apply awr_ok_x_nil
      | apply awr_ok_x_cons; [ intros y Hy; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy; rewrite ?B2a, ?B32a in Hy;
          first [ lia | left; split; [right; left; apply FPE; lia | lia] ] | ] ]. }
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR4; rename HG0 into GR4; clear HF.
  assert (KL4 : forall y, 0 <= y < 2 ^ 64 -> ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) (ms_mem msD) y).
  { intros y Hy Hy1 Hy2; apply (aview_eq_of SEGS); apply FR4; rewrite unsigned_lit_small by lia;
    intros (r & Hin & Hr); vm_compute in Hin;
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2a, ?B32a in Hr; lia |]); destruct Hin. }
  assert (KPF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR4 (KPD y Hy))).
  assert (KMF : forall y, 0 <= y < 2 ^ 64 -> ~ (re_buf e1 <= y < re_buf e1 + re_cap e1) ->
    ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y)
    by (intros y Hy H1 H2 H3 H4; rewrite KL4 by assumption; apply KMD; assumption).
  assert (HBUFF : garr8 SEGS (arm W1 (ms_mem msF)) (re_buf e1)
    (bzs (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)))).
  { apply (dnk_garr8_kept W1 (ms_mem msD) W1 (ms_mem msF) _ _ HBUFD). intros x Hx. rewrite HLBUF in Hx.
    apply KL4; lia. }
  lazymatch type of HS with
  | st_ok _ ?Ev ?ss _ => pose proof (st_ok_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_region_nth Ev ss _ 2 _ HS eq_refl) as RG2
  | st_ok_pi _ _ ?Ev ?ss _ => pose proof (st_ok_pi_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_pi_region_nth Ev ss _ 2 _ HS eq_refl) as RG2
  end.
  cbn [ms_mem restrict] in RG1, RG2.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 8 4 _ 1 RG1 B32a ltac:(cbn [In]; left; reflexivity)
    ltac:(reflexivity) ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)) as Vs.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 24 8 _ 0 RG2 B32a ltac:(cbn [In]; left; reflexivity)
    ltac:(reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as Vu.
  pose proof (drr_DMEM_move cx ly1 S1 W1 m1 (ms_mem msF) md1 _ k1 _ e1 h1 _ out1 ev1 _ LB1
    (dsp0 cx - DRAIN_FRAME - ESTACK) 1 0 [] (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)) HB HM HJ2 ltac:(unfold ESTACK; lia) ltac:(lia) KMF KPF Vs Vu
    ltac:(lia) ltac:(lia) (eq_refl : Z.of_nat (length ([] : list byte)) = 0) ltac:(lia)
    (ltac:(unfold bzs in HLBUF; rewrite length_map in HLBUF; lia) : Z.of_nat (length (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1))) = re_cap e1 - 0) HBUFF) as HMF.
  pose proof (drr_DMEM_s B RG cx _ _ _ _ _ _ _ h1
    (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p)) (dnext (dlive cx) (dxmx cx) s1) out1 ev1 _ LB1
    ltac:(rewrite NNO; reflexivity) ltac:(rewrite NOC; reflexivity) HMF) as HMF2.
  rewrite <- HSENT in HMF2.
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  apply Kdi.
  exists (ms_regs msF), ly1, S1, (ms_mem msF). eexists. eexists.
  exists (drr_eset e1 1 0 [] (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1))), h1, out1, ev1, LB1, spent. eexists. eexists. exists tl.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (KEPT 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite X3, (KEPT 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite X4, (KEPT 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite X21, (KEPT 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
    split; [rewrite X24, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X20, (KEPT 20%nat 20%bv) by (first [lia | reflexivity]); exact R20|].
    split; [rewrite X22, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, (KEPT 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|].
    split; [rewrite X8, (KEPT 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|].
    split; [rewrite X9, (KEPT 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
    split; [rewrite X18, (KEPT 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
    rewrite X26, (KEPT 26%nat 26%bv) by (first [lia | reflexivity]); exact R26. }
  split; [exact HMF2|].
  split; [unfold drr_eset; cbn [re_U]; intros []|].
  split; [unfold drr_eset; cbn [re_used]; unfold APARTIAL; lia|].
  split; [intros _; exact HDB|].
  split.
  { apply (drr_DLINK _ _ e1 _ h1 HL).
    * unfold drr_eset. cbn [re_cap]. rewrite NCAP. pose proof HL as (L1 & _). cbn [dvirt drain_b_c.ds_cap] in L1. exact L1.
    * unfold drr_eset. cbn [re_U]. rewrite NU. reflexivity.
    * unfold drr_eset. cbn [re_skip]. rewrite NSK. reflexivity.
    * unfold drr_eset. cbn [re_keys]. rewrite NH. pose proof HL as (_ & _ & _ & L4 & _). cbn [dvirt drain_b_c.ds_H] in L4. exact L4.
    * unfold drr_eset, drain_b_c.ent_ka. cbn [re_hp re_kh]. rewrite NKA. pose proof HL as (_ & _ & _ & _ & L5 & _).
      cbn [dvirt drain_b_c.ds_ka] in L5. unfold drain_b_c.ent_ka in L5. exact L5.
    * rewrite NEI. reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity. }
  split; [exact HSAME|].
  split.
  { apply (drr_DHIST cx (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))
      (dnext (dlive cx) (dxmx cx) s1) _ _ _ _ h1 LB1 0 eq_refl eq_refl ltac:(rewrite NNO; reflexivity)
      ltac:(rewrite NH; reflexivity) eq_refl HH). }
  split; [exact NJ1|].
  split; [exact HLAT | exact HBUD].
Qed.

End c.

(* ---- THE GENERIC WALK (an internal work row, the image-B twin of lib/A/W_drain_rest.v's Section cx): REST over any allocator
   relation ARx with its laws, at the room texts (the room record RP, the entry's budget kr).  The Section is
   lib/B/W_drain_cx_x.v's Section c - its variables B PST ARx MT RP MMAX RG in that order, each hypothesis that file's
   text - with the three allocator rules in their caller-context forms (this segment calls no allocator, so no
   call-site fact HCTX_* is stated), and after LAWS the generic-relation facts the walk reads:
     HP0 (no hidden head in any ARx state, a Theorem Labs lane's ruling: the table's and the buffer's shadow facts are
     W_journal_x.v's range_addressable_of_block_hp0_x / shadow_hull_vis_of_block_hp0_x) and BLKN (a live block's
     size is nonnegative, which cgif's al_blocks carried: the held keys' bytes read it).  An image byte lies in no
     live block (YCbqG.v blk_img_x, the laws' client-image field), and g_s is G_DR's head cell (HG): these keep the
     image's bytes across the segment without AR's numeric image band.  The footprint facts are lib/B/W_drain_dnrk.v's
     Section cx twins.
   The AR walk above (Section c) is unchanged.  Its lemmas are restated here with an _x suffix (each over ARx where it
   reads the relation), so no lemma's Section generalization is relied on. ---- *)
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
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
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
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* drr_DMEM_s over ARx: DMEM_x reads the round state only through ds_no and ds_ocap *)

(* drr_seat, restated (AR-free) *)
Lemma drr_seat_x : forall (W1 : world SEGS) regs1 m1 sp SA buf x n sk,
spZ regs1 = sp -> 2 ^ 46 <= sp -> alloc_ceiling <= sp -> sp + 352 <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 22 = w64 (SA + 24) -> getr regs1 19 = w64 buf -> getr regs1 24 = w64 x -> getr regs1 25 = w64 n ->
val_mem SEGS (arm W1 m1) (sp + 184) 8 6001 -> val_mem SEGS (arm W1 m1) (sp + 208) 8 (SA + 8) ->
val_mem SEGS (arm W1 m1) (sp + 232) 8 (shadow_addr (SA + 24)) -> val_mem SEGS (arm W1 m1) (sp + 240) 8 SHADOW_OFF ->
awr W1 m1 SA AENT -> val_mem SEGS (arm W1 m1) (SA + 8) 4 sk -> 0 <= sk <= 1 ->
4096 <= SA -> SA + 56 <= alloc_ceiling -> SA mod 8 = 0 ->
4096 <= buf <= 140737479966720 -> buf mod 8 = 0 -> 0 <= n <= 16384 -> 4096 <= x <= 140737479966720 ->
range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF SA 56 ->
(forall y, SA <= y < SA + 56 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (drr_extra SA sk))) drr_ss
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_rest)) m1 (seg_rom SEGS))) /\
sh_ok SEGS dj_Bx dj_SH (Eimg (Ereg regs1 (drr_extra SA sk))) (mrestrict (w_H W1) m1).
Proof.
intros W1 regs1 m1 sp SA buf x n sk Hsp Hs1 Hs0 Hs2 Hs16 R22 R19 R24 R25 F184 F208 F232 F240 HAW V8 Hsk HSA1 HSA2 HSA8
  Hb1 Hb8 Hn Hx RA HAPP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (drr_extra SA sk))).
assert (EREG : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by (intros nn r Hnn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ nn r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (U19 : bv_unsigned (ew E 19) = buf)
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite R19; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = x)
  by (rewrite (EREG 24%nat 24%bv) by (first [lia | reflexivity]); rewrite R24; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = n)
  by (rewrite (EREG 25%nat 25%bv) by (first [lia | reflexivity]); rewrite R25; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = SHADOW_OFF) by (rewrite E33; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E34 : ew E 34 = Z_to_bv 64 sk) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (U34 : bv_unsigned (ew E 34) = sk) by (rewrite E34; apply unsigned_lit_small; lia).
split.
- apply pa_entry_st_ok_full.
  + unfold drr_regs. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    rewrite R22. rewrite (den_atom E 32 SA 24 E32) by lia. reflexivity.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * unfold region_ok, drr_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ sp 184 8 (SLit 6001) 6001);
           [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside | exact F184].
      -- apply (chunk_ok_val SEGS E _ sp 208 8 (SOff 32 8) (SA + 8));
           [exact (den_atom E 32 SA 8 E32 ltac:(lia) ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
           | zside | exact F208].
      -- apply (chunk_ok_val SEGS E _ sp 232 8 _ (shadow_addr (SA + 24)));
           [exact (dj_den_sh E SA 24 E32 E33 ltac:(lia) ltac:(lia) ltac:(lia)) | | zside | exact F232].
         change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold shadow_addr, SHADOW_OFF.
         split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | ].
         assert ((SA + 24) / 8 <= SA + 24) by (apply Z.div_le_upper_bound; lia). lia.
      -- apply (chunk_ok_val SEGS E _ sp 240 8 (SOff 33 0) SHADOW_OFF);
           [exact (den_atom0 E 33 SHADOW_OFF E33 ltac:(unfold SHADOW_OFF; lia))
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | zside | exact F240].
    * unfold region_ok, drr_e1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (HAW o); unfold AENT; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ SA 8 4 (SOff 34 0) sk);
        [exact (den_atom0 E 34 sk E34 ltac:(lia)) | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | zside | exact V8].
    * unfold region_ok, drr_e3. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (HAW o). unfold AENT. lia.
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, drr_frame, drr_e1, drr_e3.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U32.
    split; [split; [right; lia | split; [right; lia | exact I]] | split; [split; [left; lia | exact I] | split; exact I]].
  + split; [|split; [exact I | exact I]].
    unfold drr_facts, dj_PTRF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U19, U24, U25, U32, U33, U34.
    assert (M16 : sp mod 2 ^ 4 = 0) by (change (2 ^ 4) with 16; exact Hs16).
    assert (M8a : SA mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact HSA8).
    assert (M8b : buf mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact Hb8).
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; try reflexivity;
      unfold SHADOW_OFF in *; lia.
- unfold sh_ok, dj_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E dj_Bx 32 SA 56 SA 0 56 RA).
  + unfold dj_Bx. apply (U_atom E 33 SHADOW_OFF E33). unfold SHADOW_OFF; lia.
  + apply (U_atom E 32 SA E32). lia.
  + lia.
  + lia.
  + intros y Hy. change (Z.min 0 56) with 0 in Hy. change (Z.max 0 56) with 56 in Hy. apply HAPP. lia.
Qed.

(* drr_aentry_move, restated (AR-free) *)
Lemma drr_aentry_move_x : forall ly S (W : world SEGS) m m' e sk u U J,
aentry_okx B ly S W m e -> 0 < re_cap e ->
(sk = 0 \/ sk = 1) -> Z.of_nat (length U) = u -> u <= re_cap e -> Z.of_nat (length J) = re_cap e - u ->
garr8 SEGS (arm W m') (re_buf e) (bzs (U ++ J)) ->
(forall p n x, In (p, n) (drr_eblks_rest e) -> p <= x < p + n -> abyte_kept W m W m' x) ->
aentry_okx B ly S W m' (drr_eset e sk u U J).
Proof.
intros ly S W m m' e sk u U J HE Hcp Hsk HU Huc HJ HGb KB.
unfold aentry_okx in HE |- *. unfold drr_eset.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
destruct HE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14).
split; [exact H1|]. split; [exact Hsk|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split; [exact HU|]. split; [exact Huc|].
split.
{ destruct H9 as [(Hc & _) | (Hc & Hin & _)]; [lia | right].
  split; [exact Hc|]. split; [exact Hin|]. split; [exact HJ | exact HGb]. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11 | right].
  split; [exact Hz|]. split; [exact Hin|]. split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (KB (re_hp e) (re_kh e)).
  - unfold drr_eblks_rest. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  - unfold bzs in Hx. rewrite length_map, (dnk_key_ptrs_len B RG) in Hx. unfold re_nheld in Hk1. lia. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [exact K1|]. split; [|exact K3].
apply (akept_garr8 W m); [|exact K2].
intros x Hx. apply (KB (key_addr k) (Z.of_nat (length (key_text k)) + 1)).
- unfold drr_eblks_rest. apply in_or_app. right.
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
- unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

(* drr_DMEM_move over ARx *)

(* drr_buf_awr over ARx *)



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
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

Lemma drr_DMEM_s_xR : forall cx Hp ly S Hp1 (W : world SEGS) m md k e h s s' out ev sent LB,
drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
DMEM_xR B PST ARx RG R cx Hp ly S Hp1 W m md k e h s out ev sent LB ->
DMEM_xR B PST ARx RG R cx Hp ly S Hp1 W m md k e h s' out ev sent LB.
Proof.
intros cx Hp ly S Hp1 W m md k e h s s' out ev sent LB H1 H2 H. unfold DMEM_xR in *. rewrite H1, H2. exact H.
Qed.

Lemma drr_DMEM_move_xR : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 lo
  sk u U J,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
alloc_ceiling <= lo -> 0 < re_cap e1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (re_buf e1 <= a < re_buf e1 + re_cap e1) -> ~ (dxSA cx + 8 <= a < dxSA cx + 12) ->
  ~ (dxSA cx + 24 <= a < dxSA cx + 32) -> ~ (lo <= a < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
val_mem SEGS (arm W1 m2) (dxSA cx + 8) 4 sk -> val_mem SEGS (arm W1 m2) (dxSA cx + 24) 8 u ->
(sk = 0 \/ sk = 1) -> 0 <= u -> Z.of_nat (length U) = u -> u <= re_cap e1 ->
Z.of_nat (length J) = re_cap e1 - u -> garr8 SEGS (arm W1 m2) (re_buf e1) (bzs (U ++ J)) ->
DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m2 md2 k2 (drr_eset e1 sk u U J) h1 sg out1 ev1 sent LB1.
Proof.
intros cx Hp kr ly1 S1 Hp1 W1 m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 lo sk u U J HB HMEM HJ2 Hlo Hcp KM HP Vs Vu
  Hsk Hu0 HUl Huc HJl HGB.
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HEOK & Hsrc & Hoth & Hgsk & Hout &
  Hlivout & Hperm).
pose proof HJ as HAR. apply ajournal_gx_AR_xR in HAR.
pose proof HB as (Hafn & _ & _ & HSAlo & HSAhi & _ & _ & _ & _ & Hj & _).
change AENT with 56 in HSAhi. change ATABLE with 896 in HSAhi.
pose proof Hafn as (_ & _ & _ & _ & _ & (_ & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hslo, Hshi.
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
pose proof asan_consts as (C1 & _).
assert (GT : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR GT) as (_ & HG4 & HGc & _).
change (req_size ATABLE) with 896 in HGc.
pose proof HEOK as (_ & _ & Hpd1 & Hpd2 & _ & _ & _ & _ & Hbufc & _).
destruct Hbufc as [(Hc0 & _) | (_ & HBin & _)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR HBin) as (_ & HB4 & HBc & _).
pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq).
(* an image byte lies in neither the table nor the buffer (the laws' client-image field, YCbqG.v blk_img_x), and
   g_s is G_DR's head cell, whose bytes are image bytes (HG): these replace AR's numeric image band *)
assert (Gtab : forall a, dxG cx <= a < dxG cx + 896 -> ~ in_img SEGS a)
  by (intros a Ha; apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ a HAR GT);
      change (req_size ATABLE) with 896; exact Ha).
assert (Gbuf : forall a, re_buf e1 <= a < re_buf e1 + req_size (re_cap e1) -> ~ in_img SEGS a)
  by (intros a Ha; exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ a HAR HBin Ha)).
assert (GSI : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> in_img SEGS a).
{ intros a Ha. refine (proj1 (HG a _)). unfold inG, G_DR. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha. }
assert (Ec0 : (re_cap e1 =? 0) = false) by (apply Z.eqb_neq; lia).
set (L2 := (dxG cx, ATABLE) :: drr_eblks_rest e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx).
assert (HP2 : Permutation (ablocks B ly1 S1) ((re_buf e1, re_cap e1) :: L2)).
{ eapply Permutation_trans; [exact Hperm|]. unfold L2, aentry_blks, drr_eblks_rest. rewrite Ec0. cbn [app].
  apply perm_swap. }
assert (HSEP : dxG cx + 896 <= re_buf e1 \/ re_buf e1 + req_size (re_cap e1) <= dxG cx).
{ assert (HP3 : Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: (re_buf e1, re_cap e1) ::
    (drr_eblks_rest e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)))
    by (eapply Permutation_trans; [exact Hperm|]; unfold aentry_blks, drr_eblks_rest; rewrite Ec0; cbn [app];
        apply Permutation_refl).
  pose proof (sep_blocks_perm_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ _ HAR HP3) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. exact Hd. }
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (re_buf e1 <= a < re_buf e1 + req_size (re_cap e1)) ->
  ~ (dxG cx <= a < dxG cx + 896) -> ~ (lo <= a < dsp0 cx - DRAIN_FRAME) -> abyte_kept W1 m1 W1 m2 a).
{ intros a Ha H1 H2 H3. split; [apply KM; lia|]. unfold arm. apply (writable_kept (w_H W1) m1 m2 a (HP a)). }
assert (HKX : forall a, dnk_low cx a -> dnx_low (re_buf e1, re_cap e1) a -> abyte_kept W1 m1 W1 m2 a).
{ intros a (Ha & Ht) (_ & Hb). cbn [fst snd] in Hb. apply HK; [lia | exact Hb | change ATABLE with 896 in Ht; exact Ht | lia]. }
assert (HKF : forall a, dsp0 cx - DRAIN_FRAME <= a < 2 ^ 64 -> abyte_kept W1 m1 W1 m2 a)
  by (intros a Ha; apply HK; lia).
assert (HKI : forall a, in_img SEGS a -> abyte_kept W1 m1 W1 m2 a).
{ intros a Ha. pose proof (pa_img_range a Ha) as Hai.
  apply HK; [lia | intros Hb; exact (Gbuf a Hb Ha) | intros Hb; exact (Gtab a Hb Ha) | lia]. }
assert (HVMF : forall a v, dsp0 cx - DRAIN_FRAME <= a -> a + 8 <= dsp0 cx ->
  val_mem SEGS (arm W1 m1) a 8 v -> val_mem SEGS (arm W1 m2) a 8 v).
{ intros a v H1 H2 Hv. apply (akept_vm W1 m1); [|exact Hv]. intros x Hx. apply HKF. lia. }
assert (HVMG : forall a v, rg_s RG <= a -> a + 4 <= rg_s RG + 4 * ASRC ->
  val_mem SEGS (arm W1 m1) a 4 v -> val_mem SEGS (arm W1 m2) a 4 v).
{ intros a v H1 H2 Hv. apply (akept_vm W1 m1); [|exact Hv]. intros x Hx. cbn in Hx. apply HKI, GSI. lia. }
assert (HBIN : forall b, In b (aentry_blks e1) \/ In b (asrc_blks h1) \/ In b (aout_blks (drain_b_c.ds_ocap sg) out1) ->
  In b (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ dxrest cx)).
{ intros b [Hb | [Hb | Hb]]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb |].
  right; apply in_or_app; right; apply in_or_app; left; exact Hb. }
assert (HBIN2 : forall b, In b (asrc_blks h1) \/ In b (aout_blks (drain_b_c.ds_ocap sg) out1) -> In b L2).
{ intros b [Hb | Hb]; unfold L2; right; apply in_or_app; right; apply in_or_app;
    [left; exact Hb | right; apply in_or_app; left; exact Hb]. }
split; [exact HJ2|].
split.
{ intros a Ha. pose proof Ha as (sg0 & Hsg & _ & Hr).
  rewrite (proj1 (HKI a (ex_intro _ sg0 (conj Hsg Hr)))). exact (Hrom a Ha). }
split; [intros a Ha1 Ha2 Ha3 Ha4; apply HP; exact (Hpres a Ha1 Ha2 Ha3 Ha4)|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  repeat match type of HFR with _ /\ _ => let A := fresh "A" in destruct HFR as [A HFR] end.
  repeat match goal with |- _ /\ _ => split end;
    first [ apply HVMF; [lia | lia | assumption]
          | intros i Hi; apply HVMF; [unfold DR_SAVE_OFF; lia | unfold DR_SAVE_OFF; lia | exact (HFR i Hi)] ]. }
split.
{ apply (drr_entry_set (w_H W1) m1 m2 (dxSA cx) e1 sk u U J Hgarr Hpd1 Hpd2); [| exact Vs | exact Vu | lia | lia].
  intros y Hy Hy1 Hy2. apply KM; lia. }
split; [intros i Hi; unfold arm; apply (writable_kept (w_H W1) m1 m2 _ (HP _)); exact (Hawr i Hi)|].
split.
{ apply (drr_aentry_move_x ly1 S1 W1 m1 m2 e1 sk u U J HEOK Hcp Hsk HUl Huc HJl HGB).
  intros pb nb x Hin Hx.
  assert (Hin1 : In (pb, nb) (aentry_blks e1))
    by (unfold aentry_blks; rewrite Ec0; right; exact Hin).
  assert (HinL2 : In (pb, nb) L2) by (unfold L2; right; apply in_or_app; left; exact Hin).
  assert (Hab : In (pb, nb) (ablocks B ly1 S1)) by (apply (Permutation_in _ (Permutation_sym HP2)); right; exact HinL2).
  pose proof (BLKN _ _ _ _ _ _ _ _ HAR Hab) as Hnb.
  pose proof (req_size_pos nb ltac:(lia)) as (_ & Hrqb).
  apply HKX.
  - exact (proj1 (dnk_low_blk_x B ARx RG LAWS HG HGSB cx ly1 S1 Hp1 W1 m1 md1 _ pb nb x HAR Hperm
      ltac:(apply in_or_app; left; exact Hin1) ltac:(lia))).
  - exact (proj1 (dnx_low_blk_x B ARx RG LAWS HG HGSB (re_buf e1, re_cap e1) ly1 S1 Hp1 W1 m1 md1 L2 pb nb x HAR HP2 HinL2
      ltac:(lia))). }
split.
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m2 (dHA RG cx) h1 Hsrc);
    [|exact (dnk_asrc_blks_in B RG HGSB ly1 S1 W1 m1 (dHA RG cx) h1 Hsrc)].
  intros r Hr a Ha. apply HKX.
  - exact (proj1 (dnk_fp_src_x B ARx RG LAWS HG HRGD HGSB HSD HSM cx ly1 S1 Hp1 W1 m1 md1 _ h1 HAR Hperm
      (fun b Hb => HBIN b (or_intror (or_introl Hb))) GT Hj Hsrc r Hr a Ha)).
  - exact (proj1 (dnx_fp_src_x B ARx RG LAWS HG HRGD HGSB HSD HSM (re_buf e1, re_cap e1) cx ly1 S1 Hp1 W1 m1 md1 L2 h1 HAR HP2
      (fun b Hb => HBIN2 b (or_introl Hb)) HBin Hj Hsrc r Hr a Ha)). }
split.
{ intros i Hi Hne. destruct (Hoth i Hi Hne) as (f & o & V1 & V2 & Hdis). exists f, o.
  assert (Hi4 : Z.of_nat i < 4) by lia. unfold ASRC in *.
  split; [apply HVMG; [lia | lia | exact V1]|].
  split; [apply HVMG; [lia | lia | exact V2] | exact Hdis]. }
split.
{ intros x Hx1 Hx2. pose proof (Hgsk x Hx1 Hx2) as (Hv & Hw).
  pose proof (HKI x (GSI x Hx1)) as (Hk1 & Hk2).
  split; [rewrite Hk1; exact Hv|]. intros Hwr. exact (Hk2 (Hw Hwr)). }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m2); [exact Hout| |].
  - intros r Hr a Ha. apply HKX.
    + exact (proj1 (dnk_fp_out_x B ARx MMAX RG LAWS HG HGO HRGD HGSB HMMAX HSD HSM cx ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ _ HAR Hperm
        (fun b Hb => HBIN b (or_intror (or_intror Hb))) Hout r Hr a Ha)).
    + exact (dnx_fp_out_x B ARx RG LAWS HG HGO HGSB (re_buf e1, re_cap e1) ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ L2 HAR HP2
        (fun b Hb => HBIN2 b (or_intror Hb)) Hout r Hr a Ha).
  - exact (dnk_aout_blks_in B RG HGSB ly1 S1 W1 m1 _ _ _ _ _ _ Hout). }
split; [exact Hlivout | exact Hperm].
Qed.

Lemma drr_buf_awr_xR : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 a,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DMEM_xR B PST ARx RG R cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
(re_cap e1 = 8192 \/ re_cap e1 = 16384) -> In (re_buf e1, re_cap e1) (ablocks B ly1 S1) ->
re_buf e1 <= a < re_buf e1 + re_cap e1 ->
(inFP (dFP cx) a /\ exists b nb, In (b, nb) (ablocks B ly1 S1) /\ b <= a < b + req_size nb) \/
in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a.
Proof.
intros cx Hp kr ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 a HB HM Hcap HBin Ha.
pose proof HM as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm).
pose proof HJ as HAR. apply ajournal_gx_AR_xR in HAR.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm0 & _).
pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq).
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y})
  by (intros [x1 x2] [y1 y2]; destruct (Z.eq_dec x1 y1), (Z.eq_dec x2 y2);
      [left; congruence | right; congruence | right; congruence | right; congruence]).
destruct (in_dec Hdec (re_buf e1, re_cap e1) (ablocks B (dxly cx) (dxS cx))) as [Hin0 | Hnin0].
- left. split; [|exists (re_buf e1), (re_cap e1); split; [exact HBin | lia]].
  apply (Permutation_in _ Hperm0) in Hin0. destruct Hin0 as [Heq | Hin0].
  + injection Heq as _ Hc. unfold ATABLE in Hc. lia.
  + apply in_app_or in Hin0 as [Hin0 | Hin0].
    * exists (re_buf e1, re_buf e1 + req_size (re_cap e1)). split; [|cbn [fst snd]; lia].
      unfold dFP, dr_fp. right. unfold ablocks_fp. apply (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ (re_buf e1, re_cap e1)).
      apply in_or_app. left. exact Hin0.
    * apply in_app_or in Hin0 as [Hin0 | Hin0].
      -- exists (re_buf e1, re_buf e1 + req_size (re_cap e1)). split; [|cbn [fst snd]; lia].
         unfold dFP, dr_fp. right. unfold ablocks_fp. apply (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ (re_buf e1, re_cap e1)).
         apply in_or_app. right. apply in_or_app. left. exact Hin0.
      -- apply in_app_or in Hin0 as [Hin0 | Hin0].
         ++ exists (re_buf e1, re_buf e1 + req_size (re_cap e1)). split; [|cbn [fst snd]; lia].
            unfold dFP, dr_fp. right. unfold ablocks_fp. apply (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ (re_buf e1, re_cap e1)).
            apply in_or_app. right. apply in_or_app. right. exact Hin0.
         ++ (* the buffer is in the rest of the blocks too: twice in the round's blocks, impossible *)
            exfalso. destruct (in_split _ _ Hin0) as (r1 & r2 & Er).
            assert (Ec0 : (re_cap e1 =? 0) = false) by (apply Z.eqb_neq; lia).
            assert (HP2 : Permutation (ablocks B ly1 S1)
              ((re_buf e1, re_cap e1) :: (re_buf e1, re_cap e1) :: (dxG cx, ATABLE) ::
               ((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
                map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
               asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap sg) out1 ++ r1 ++ r2)).
            { eapply Permutation_trans; [exact Hperm|].
              unfold aentry_blks. rewrite Ec0, Er. cbn [app].
              eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
              eapply Permutation_trans; [apply perm_skip | apply perm_swap].
              rewrite !app_assoc. apply Permutation_sym, Permutation_middle. }
            pose proof (sep_blocks_perm_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ _ HAR HP2) as Hd.
            unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
- right. exists (re_buf e1), (re_cap e1). split; [exact HBin|]. split; [exact Hnin0 | lia].
Qed.

Theorem dr_rest_xR : dr_rest_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold dr_rest_stmt_xR. intros cx Hp kr s1 D p W1 c1 HB HDLR Kdi.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HDLR as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl &
  Hc1 & HRG & R26 & R24 & R25 & R19 & HDB & HCAP & Hbnd & Hnz & HDLC & HFUT).
subst c1.
pose proof HRG as (Hsp & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & HFR).
pose proof HDLC as HLC. unfold DLC_xR, LCORE_xR in HLC.
destruct HLC as (HM & HL & HSAME & HH & HRS & HBUD).
pose proof HM as (HJ & Hrom & _ & _ & _ & Hgarr & Hawr & HEOK & _ & _ & _ & _ & _ & Hperm).
pose proof HJ as HAR. apply ajournal_gx_AR_xR in HAR.
pose proof HB as (Hafn & _ & HGB & HSAlo & HSAhi & HSA8 & _ & _ & _ & Hj & _).
change AENT with 56 in HSAhi. change ATABLE with 896 in HSAhi.
pose proof Hafn as (_ & _ & _ & Hgp & Htp & (Hal16 & _ & Hcl & Hslo & Hshi & H47 & _) & _).
change (spZ (dxregs cx)) with (dsp0 cx) in Hal16, Hslo, Hshi.
assert (HDS : DRAIN_STK_x = 17008) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR GT) as (HG16 & HG4 & HGc & HGapp & _).
change (req_size ATABLE) with 896 in HGc, HGapp.
pose proof HEOK as (Heof & Hskp & Hpd1 & Hpd2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & _).
destruct Hbufc as [(Hc0 & _) | (Hcpos & HBin & Hjunk & Hbgarr)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR HBin) as (HB16 & HB4 & HBc & HBapp & HBpres & _).
pose proof (req_size_pos (re_cap e1) ltac:(lia)) as (_ & Hrq).
pose proof HL as (_ & HU & _).
cbn [dvirt drain_b_c.ds_u] in HU.
assert (HUL : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HU; unfold bzs; rewrite length_map; exact HUlen).
assert (Hcap16 : re_cap e1 <= 16384) by (destruct Hcapr as [H|[H|H]]; lia).
pose proof HDB as (Hdb1 & Hdb2 & Hdb3). unfold DCEIL in Hdb2.
pose proof Hbnd as (Hpl & _).
pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F184 & _ & F208 & _ & _ & F232 & F240 & _).
pose proof (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE (dxSA cx) 56 HAR GT
  HSAlo ltac:(change (req_size ATABLE) with 896; lia)) as RA.
assert (HAPP : forall y, dxSA cx <= y < dxSA cx + 56 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)).
{ intros y Hy. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
destruct (drr_seat_x W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_buf e1) (re_buf e1 + Z.of_nat p)
  (Z.of_nat (length (dW s1) - p)) (re_skip e1)
  Hsp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; rewrite HDF; reflexivity)
  R22 R19 R24 R25 F184 F208 F232 F240 Hawr
  (dnk_entry_skip (arm W1 m1) (dxSA cx) e1 Hgarr Hpd1 ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia) HSA8
  ltac:(lia) Hdb3 ltac:(lia) ltac:(lia) RA HAPP) as [HS SHOK].
remember (Eimg (Ereg regs1 (drr_extra (dxSA cx) (re_skip e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by (intros nn r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ nn r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_skip e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
clear HE.
assert (B2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (B32 : bv_unsigned (ew E 32) = dxSA cx) by (rewrite E32; apply unsigned_lit_small; lia).
assert (FPE : forall y, dxSA cx <= y < dxSA cx + 56 ->
  inFP (dFP cx) y /\ exists b nb, In (b, nb) (ablocks B ly1 S1) /\ b <= y < b + req_size nb).
{ intros y Hy. split.
  - exists (dxSA cx, dxSA cx + AENT). split; [unfold dFP, dr_fp; left; reflexivity | cbn [fst snd]; unfold AENT; lia].
  - exists (dxG cx), ATABLE. split; [exact GT | change (req_size ATABLE) with 896; lia]. }
unfold cfg_at. change (w64 (BASE + A_dr_rest)) with (Z_to_bv 64 (BASE + A_dr_rest)).
paj_run_tok_xR RUNG HS HJ SHOK dj_Bspan.
{ lazymatch goal with |- awr_ok_x ?E0 ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x E0 rs' G XO OUT stk sp0 fp b0 bc ly own) end.
  repeat first [ apply awr_ok_x_nil
    | apply awr_ok_x_cons; [ intros y Hy; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy; rewrite ?B2, ?B32 in Hy;
        first [ lia | left; split; [right; left; apply FPE; lia | lia] ] | ] ]. }
lazymatch type of HS with context [restrict _ ?y] => rename y into msC end.
rename HFr into FR1; rename HG0 into GR1; clear HF.
assert (HSEP : dxG cx + 896 <= re_buf e1 \/ re_buf e1 + req_size (re_cap e1) <= dxG cx).
{ assert (Ec0 : (re_cap e1 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (HP2 : Permutation (ablocks B ly1 S1) ((dxG cx, ATABLE) :: (re_buf e1, re_cap e1) ::
    (((if re_hp e1 =? 0 then [] else [(re_hp e1, re_kh e1)]) ++
      map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)) ++
     asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p)
       (dloc cx s1 p))) out1 ++ dxrest cx))).
  { eapply Permutation_trans; [exact Hperm|]. unfold aentry_blks. rewrite Ec0. cbn [app]. apply Permutation_refl. }
  pose proof (sep_blocks_perm_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ _ HAR HP2) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. exact Hd. }
(* the first run wrote only s->used *)
assert (KL1 : forall y, 0 <= y < 2 ^ 64 -> ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
  aview SEGS (w_H W1) (ms_mem msC) y = aview SEGS (w_H W1) m1 y).
{ intros y Hy Hy1 Hy2; apply (aview_eq_of SEGS); apply FR1; rewrite unsigned_lit_small by lia;
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2, ?B32 in Hr; lia |]); destruct Hin. }
assert (KP1 : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msC) y)
  by (intros y Hy; exact (apresent_grows _ _ _ _ GR1 Hy)).
pose proof HJ as HARC. apply ajournal_gx_AR_xR in HARC.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Usp0 : spZ (ms_regs msC) = dsp0 cx - DRAIN_FRAME).
{ unfold spZ at 1. rewrite Q2, (EREG 2%nat 2%bv) by (first [lia | reflexivity]). exact Hsp. }
set (n := Z.of_nat (length (dW s1) - p)) in *.
assert (Hnp : Z.of_nat p + n = re_used e1) by (unfold n; rewrite Nat2Z.inj_sub by lia; lia).
assert (Hn0 : 0 <= n) by (unfold n; lia).
assert (HUJ : Z.of_nat (length (bzs (re_U e1 ++ re_junk e1))) = re_cap e1)
  by (unfold bzs; rewrite length_map, length_app; lia).
(* the buffer's bytes, as the reader sees them at the call *)
assert (BYTEC : forall j, (j < length (bzs (re_U e1 ++ re_junk e1)))%nat ->
  aview SEGS (w_H W1) (ms_mem msC) (re_buf e1 + Z.of_nat j) = Some (nth j (bzs (re_U e1 ++ re_junk e1)) 0)).
{ intros j Hjl. rewrite KL1 by (unfold AENT, ATABLE in *; lia).
  rewrite <- (app_nil_r (bzs (re_U e1 ++ re_junk e1))) in Hbgarr.
  pose proof (dj_buf_byte (w_H W1) m1 (re_buf e1) (bzs (re_U e1 ++ re_junk e1)) [] j Hbgarr Hjl) as Rb.
  exact Rb. }
assert (HVIS : forall y, re_buf e1 <= y < re_buf e1 + re_cap e1 -> exists v, aview SEGS (w_H W1) (ms_mem msC) y = Some v).
{ intros y Hy. replace y with (re_buf e1 + Z.of_nat (Z.to_nat (y - re_buf e1))) by lia.
  rewrite BYTEC by lia. eexists; reflexivity. }
assert (HNIMG : forall y, re_buf e1 <= y < re_buf e1 + re_cap e1 -> ~ in_img SEGS y)
  by (intros y Hy; exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ y HAR HBin ltac:(lia))).
(* an image byte lies in no live block (YCbqG.v blk_img_x), so not in the table; this replaces AR's numeric band
   blk_off_imgP, which ARx does not give *)
assert (Gtab : forall y, dxG cx <= y < dxG cx + 896 -> ~ in_img SEGS y)
  by (intros y Hy; apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ y HAR GT);
      change (req_size ATABLE) with 896; exact Hy).
assert (Hromc : rom_view SEGS W1 (ms_mem msC)).
{ intros y Hy. pose proof Hy as (sg0 & Hsg & _ & Hr). pose proof (pa_img_range y (ex_intro _ sg0 (conj Hsg Hr))) as Hyi.
  assert (Gy : ~ (dxG cx <= y < dxG cx + 896)) by (intros Hg; exact (Gtab y Hg (ex_intro _ sg0 (conj Hsg Hr)))).
  rewrite KL1 by lia. exact (Hrom y Hy). }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 [] ESTACK (SIGMA WS_asan_memmove)
    (fun y => re_buf e1 <= y < re_buf e1 + n)
    (fun regs' mem' => getr regs' 10 = w64 (re_buf e1) /\
       forall i, 0 <= i < n -> aview SEGS (w_H W1) mem' (re_buf e1 + i) =
         aview SEGS (w_H W1) (ms_mem msC) (re_buf e1 + Z.of_nat p + i))
    W1 (ms_regs msC) (ms_mem msC) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) []
    ly1 S1 Hp1 _ k1 (-352) (Z_to_bv 64 (BASE + 6928))).
  - exact HG.
  - reflexivity.
  - exact HJ.
  - rewrite Usp0, HDF. lia.
  - reflexivity.
  - lia.
  - lia.
  - rewrite HDS. unfold ESTACK; lia.
  - rewrite Q3, (EREG 3%nat 3%bv) by (first [lia | reflexivity]). rewrite R3. exact Hgp.
  - rewrite Q4, (EREG 4%nat 4%bv) by (first [lia | reflexivity]). rewrite R4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros y. destruct (Z_lt_le_dec y (re_buf e1)); [right; lia|].
    destruct (Z_lt_le_dec y (re_buf e1 + n)); [left; lia | right; lia].
  - intros y Hy HGy. exfalso. exact (HNIMG y ltac:(lia) (proj1 (HG y HGy))).
  - intros y Hy _. split; [|lia].
    destruct (drr_buf_awr_xR cx Hp kr ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 _ out1 ev1 _ LB1 y HB HM
      ltac:(destruct Hcapr as [H|[H|H]]; lia) HBin ltac:(lia)) as [Ha | Ha];
      [right; left; exact Ha | right; right; left; exact Ha].
  - intros HPRE2 _.
    apply (AMEMMOVE ly1 S1 Hp1 W1 (ms_regs msC) (ms_mem msC) _ (re_buf e1) (re_buf e1 + Z.of_nat p) n HPRE2).
    + rewrite Q10, (EREG 19%nat 19%bv) by (first [lia | reflexivity]). exact R19.
    + rewrite Q11, (EREG 24%nat 24%bv) by (first [lia | reflexivity]). exact R24.
    + rewrite Q12, (EREG 25%nat 25%bv) by (first [lia | reflexivity]). exact R25.
    + lia.
    + lia.
    + lia.
    + intros y Hy. split; [|split].
      * destruct (HVIS y ltac:(lia)) as (v & Hv).
        exact (dnk_writable_view (w_H W1) (ms_mem msC) y v ltac:(lia) Hv
          (fun Hr => HNIMG y ltac:(lia) (let '(ex_intro _ sg0 (conj Hsg (conj _ Hrr))) := Hr in
             ex_intro _ sg0 (conj Hsg Hrr)))).
      * exact (proj2 (HBpres y ltac:(lia))).
      * rewrite Usp0. unfold ESTACK. lia.
    + unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1) _ n
        HARC HBin);
        lia.
    + intros Hpos.
      apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1) _ n
        HARC HBin);
        lia.
    + lia.
    + lia.
    + intros y Hy. split; [destruct (HVIS y ltac:(lia)) as (v & Hv); rewrite Hv; discriminate|].
      rewrite Usp0. unfold ESTACK. lia.
    + unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1) _ n
        HARC HBin);
        lia.
    + intros Hpos.
      apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem msC) _ (re_buf e1) (re_cap e1) _ n
        HARC HBin);
        lia.
    + exact Hromc.
    + intros Hpos. pose proof (@ASAN_CEIL_range rc) as (Hcc & _). pose proof HBapp as (Ha0 & HLH).
      split; destruct HLH as [HLo | [HH1 HH2]];
        unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; [left; lia | right; lia | left; lia | right; lia].
    + intros y Hy. exact (HNIMG y ltac:(lia)). }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HR10 & HMV) & Hfr2 & Hpres2).
assert (FR2 : forall y, 0 <= y < 2 ^ 64 -> ~ (re_buf e1 <= y < re_buf e1 + n) ->
  ~ (dsp0 cx + -352 - ESTACK <= y < dsp0 cx + -352) -> aview SEGS (w_H W1) mem2 y = aview SEGS (w_H W1) (ms_mem msC) y)
  by exact Hfr2.
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 2%nat (dsp0 cx - DRAIN_FRAME));
      [exact B2 | intros y Hy; apply FR2; [lia | lia | unfold ESTACK; lia] | exact Hpres2].
  - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 32%nat (dxSA cx));
      [exact B32 | intros y Hy; apply FR2; [lia | lia | unfold ESTACK; lia] | exact Hpres2].
  - apply (region_kept_aview E (w_H W1) (ms_mem msC) mem2 32%nat (dxSA cx));
      [exact B32 | intros y Hy; apply FR2; [lia | lia | unfold ESTACK; lia] | exact Hpres2]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
assert (E32a : ew Ea 32 = Z_to_bv 64 (dxSA cx)) by (rewrite OLDa by lia; exact E32).
assert (E33a : ew Ea 33 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDa by lia; exact E33).
assert (B2a : bv_unsigned (ew Ea 2) = dsp0 cx - DRAIN_FRAME) by (rewrite OLDa by lia; exact B2).
assert (B32a : bv_unsigned (ew Ea 32) = dxSA cx) by (rewrite OLDa by lia; exact B32).
pose proof HJ2 as HAR2. apply ajournal_gx_AR_xR in HAR2.
assert (SHOK2 : sh_ok SEGS dj_Bx dj_SH Ea (mrestrict (w_H W1) mem2)).
{ unfold sh_ok, dj_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) mem2 Ea dj_Bx 32 (dxSA cx) 56 (dxSA cx) 0 56
    (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 mem2 md2 (dxG cx) ATABLE (dxSA cx) 56 HAR2 GT
      HSAlo ltac:(change (req_size ATABLE) with 896; lia))).
  + unfold dj_Bx. apply (U_atom Ea 33 SHADOW_OFF E33a). unfold SHADOW_OFF; lia.
  + apply (U_atom Ea 32 (dxSA cx) E32a). lia.
  + lia.
  + lia.
  + intros y Hy. change (Z.min 0 56) with 0 in Hy. change (Z.max 0 56) with 56 in Hy. apply HAPP. lia. }
paj_run_tok_xR RUNG HS HJ2 SHOK2 dj_Bspan.
{ lazymatch goal with |- awr_ok_x ?E0 ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x E0 rs' G XO OUT stk sp0 fp b0 bc ly own) end.
  repeat first [ apply awr_ok_x_nil
    | apply awr_ok_x_cons; [ intros y Hy; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy; rewrite ?B2a, ?B32a in Hy;
        first [ lia | left; split; [right; left; apply FPE; lia | lia] ] | ] ]. }
lazymatch type of HS with context [restrict _ ?y] => rename y into msD end.
rename HFr into FR3; rename HG0 into GR3; clear HF.
assert (KL3 : forall y, 0 <= y < 2 ^ 64 -> ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
  aview SEGS (w_H W1) (ms_mem msD) y = aview SEGS (w_H W1) mem2 y).
{ intros y Hy Hy1 Hy2; apply (aview_eq_of SEGS); apply FR3; rewrite unsigned_lit_small by lia;
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2a, ?B32a in Hr; lia |]); destruct Hin. }
assert (KPD : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msD) y)
  by (intros y Hy; exact (apresent_grows _ _ _ _ GR3 (Hpres2 y (KP1 y Hy)))).
assert (KMD : forall y, 0 <= y < 2 ^ 64 -> ~ (re_buf e1 <= y < re_buf e1 + re_cap e1) ->
  ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
  ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) (ms_mem msD) y = aview SEGS (w_H W1) m1 y).
{ intros y Hy H1 H2 H3 H4. rewrite KL3 by assumption. rewrite FR2 by (unfold ESTACK in *; lia). apply KL1; assumption. }
assert (HBUFD : garr8 SEGS (arm W1 (ms_mem msD)) (re_buf e1)
  (bzs (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)))).
{ apply (drr_buf_moved (w_H W1) (ms_mem msD) (re_buf e1) (re_U e1) (re_junk e1) p n); [lia | lia | |].
  - intros i Hi. rewrite KL3 by lia. rewrite (HMV i Hi).
    replace (re_buf e1 + Z.of_nat p + i) with (re_buf e1 + Z.of_nat (p + Z.to_nat i)) by lia.
    apply BYTEC. unfold bzs. rewrite length_map, length_app. lia.
  - intros i Hi. rewrite length_app in Hi. rewrite KL3 by lia. rewrite FR2 by (unfold ESTACK in *; lia).
    replace (re_buf e1 + i) with (re_buf e1 + Z.of_nat (Z.to_nat i)) by lia.
    apply BYTEC. unfold bzs. rewrite length_map, length_app. lia. }
assert (HLBUF : Z.of_nat (length (bzs (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)))) = re_cap e1).
{ unfold bzs. rewrite length_map, length_app, !length_skipn, length_app. lia. }
destruct (drr_next_model cx s1 D p HRS Hbnd Hnz) as (HQ & NCAP & NU & NSK & NH & NKA & NNO & NOC & NEI & HSENT & NJ1).
unfold dlfut in HFUT. rewrite HQ in HFUT. cbv zeta in HFUT. cbn [drain_b_c.lines_run fst snd] in HFUT.
destruct HFUT as (tl2 & HLAT & Htl). cbn [app] in Htl. rewrite <- Htl in HLAT.
rewrite HQ in HH. cbn [length] in HH. change (Z.of_nat 0) with 0 in HH. rewrite <- HSENT in HH.
assert (E34a : ew Ea 34 = Z_to_bv 64 (re_skip e1)) by (rewrite OLDa by lia; exact E34).
assert (KEPT : forall (nn : nat) (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew Ea nn = getr regs1 r)
  by (intros nn r Hn Hr; rewrite OLDa by lia; exact (EREG nn r Hn Hr)).
assert (E25a : ew Ea 25 = Z_to_bv 64 n)
  by (rewrite (KEPT 25%nat 25%bv) by (first [lia | reflexivity]); exact R25).
psrr_branch_tok RUNG BRR HS SHOK2 dj_Bspan.
- (* the rest fits (used < 6001): s->used = |W| - p, DI *)
  assert (Hn6 : n < 6001).
  { rewrite W_traps.trap_br_ltu in Hc. rewrite (U_atom Ea 25 n E25a) in Hc by lia. rewrite (U_lit Ea 6001) in Hc by lia.
    apply Z.ltb_lt in Hc. exact Hc. }
  clear Hc.
  assert (HBIG : Nat.ltb LINE_LIMIT (length (dW s1) - p) = false).
  { apply Nat.ltb_ge. apply Nat2Z.inj_le. change (Z.of_nat LINE_LIMIT) with 6000.
    assert (Hz : Z.of_nat (length (dW s1) - p) < 6001) by exact Hn6. lia. }
  rewrite HBIG in NU, NSK.
  paj_run_to_tok_xR RUNTOG HS HJ2 SHOK2 dj_Bspan A_dr_top.
  { lazymatch goal with |- awr_ok_x ?E0 ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok_x E0 rs' G XO OUT stk sp0 fp b0 bc ly own) end.
    repeat first [ apply awr_ok_x_nil
      | apply awr_ok_x_cons; [ intros y Hy; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy; rewrite ?B2a, ?B32a in Hy;
          first [ lia | left; split; [right; left; apply FPE; lia | lia] ] | ] ]. }
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR4; rename HG0 into GR4; clear HF.
  assert (KL4 : forall y, 0 <= y < 2 ^ 64 -> ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) (ms_mem msD) y).
  { intros y Hy Hy1 Hy2; apply (aview_eq_of SEGS); apply FR4; rewrite unsigned_lit_small by lia;
    intros (r & Hin & Hr); vm_compute in Hin;
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2a, ?B32a in Hr; lia |]); destruct Hin. }
  assert (KPF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR4 (KPD y Hy))).
  assert (KMF : forall y, 0 <= y < 2 ^ 64 -> ~ (re_buf e1 <= y < re_buf e1 + re_cap e1) ->
    ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y)
    by (intros y Hy H1 H2 H3 H4; rewrite KL4 by assumption; apply KMD; assumption).
  assert (HBUFF : garr8 SEGS (arm W1 (ms_mem msF)) (re_buf e1)
    (bzs (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)))).
  { apply (dnk_garr8_kept W1 (ms_mem msD) W1 (ms_mem msF) _ _ HBUFD). intros x Hx. rewrite HLBUF in Hx.
    apply KL4; lia. }
  lazymatch type of HS with
  | st_ok _ ?Ev ?ss _ => pose proof (st_ok_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_region_nth Ev ss _ 2 _ HS eq_refl) as RG2
  | st_ok_pi _ _ ?Ev ?ss _ => pose proof (st_ok_pi_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_pi_region_nth Ev ss _ 2 _ HS eq_refl) as RG2
  end.
  cbn [ms_mem restrict] in RG1, RG2.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 8 4 _ (re_skip e1) RG1 B32a ltac:(cbn [In]; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E34a; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)) as Vs.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 24 8 _ n RG2 B32a ltac:(cbn [In]; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E25a; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as Vu.
  pose proof (drr_DMEM_move_xR cx Hp kr ly1 S1 Hp1 W1 m1 (ms_mem msF) md1 _ k1 _ e1 h1 _ out1 ev1 _ LB1
    (dsp0 cx - DRAIN_FRAME - ESTACK) (re_skip e1) n (skipn p (re_U e1)) (skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)) HB HM HJ2 ltac:(unfold ESTACK; lia) ltac:(lia) KMF KPF Vs Vu
    ltac:(lia) ltac:(lia) (ltac:(rewrite length_skipn; lia) : Z.of_nat (length (skipn p (re_U e1))) = n)
    ltac:(lia) (ltac:(rewrite length_skipn, length_app; lia) : Z.of_nat (length (skipn (Z.to_nat n) (re_U e1 ++ re_junk e1))) = re_cap e1 - n) HBUFF) as HMF.
  pose proof (drr_DMEM_s_xR cx Hp _ _ _ _ _ _ _ _ h1
    (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p)) (dnext (dlive cx) (dxmx cx) s1) out1 ev1 _ LB1
    ltac:(rewrite NNO; reflexivity) ltac:(rewrite NOC; reflexivity) HMF) as HMF2.
  rewrite <- HSENT in HMF2.
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  apply Kdi.
  exists (ms_regs msF), ly1, S1, Hp1, (ms_mem msF). eexists. eexists.
  exists (drr_eset e1 (re_skip e1) n (skipn p (re_U e1)) (skipn (Z.to_nat n) (re_U e1 ++ re_junk e1))), h1, out1, ev1, LB1, spent. eexists. eexists. exists tl.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (KEPT 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite X3, (KEPT 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite X4, (KEPT 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite X21, (KEPT 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
    split; [rewrite X24, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X20, (KEPT 20%nat 20%bv) by (first [lia | reflexivity]); exact R20|].
    split; [rewrite X22, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, (KEPT 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|].
    split; [rewrite X8, (KEPT 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|].
    split; [rewrite X9, (KEPT 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
    split; [rewrite X18, (KEPT 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
    rewrite X26, (KEPT 26%nat 26%bv) by (first [lia | reflexivity]); exact R26. }
  split; [exact HMF2|].
  split.
  { unfold drr_eset. cbn [re_U]. intros Hin. apply (in_map bz) in Hin.
    replace (bz (Z_to_bv 8 0)) with 0 in Hin by reflexivity. rewrite <- skipn_map in Hin. fold (bzs (re_U e1)) in Hin.
    rewrite HU in Hin. apply In_nth_error in Hin as (i & Hi). rewrite nth_error_skipn in Hi.
    exact (Hnz (p + i)%nat ltac:(lia) Hi). }
  split; [unfold drr_eset; cbn [re_used]; unfold APARTIAL; lia|].
  split; [intros _; exact HDB|].
  split.
  { apply (drr_DLINK _ _ e1 _ h1 HL).
    * unfold drr_eset. cbn [re_cap]. rewrite NCAP. pose proof HL as (L1 & _). cbn [dvirt drain_b_c.ds_cap] in L1. exact L1.
    * unfold drr_eset. cbn [re_U]. rewrite NU. unfold bzs. rewrite <- skipn_map. fold (bzs (re_U e1)). rewrite HU. reflexivity.
    * unfold drr_eset. cbn [re_skip]. rewrite NSK. pose proof HL as (_ & _ & L3 & _). cbn [dvirt drain_b_c.ds_skip] in L3. exact L3.
    * unfold drr_eset. cbn [re_keys]. rewrite NH. pose proof HL as (_ & _ & _ & L4 & _). cbn [dvirt drain_b_c.ds_H] in L4. exact L4.
    * unfold drr_eset, drain_b_c.ent_ka. cbn [re_hp re_kh]. rewrite NKA. pose proof HL as (_ & _ & _ & _ & L5 & _).
      cbn [dvirt drain_b_c.ds_ka] in L5. unfold drain_b_c.ent_ka in L5. exact L5.
    * rewrite NEI. reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity. }
  split; [exact HSAME|].
  split.
  { apply (drr_DHIST cx (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))
      (dnext (dlive cx) (dxmx cx) s1) _ _ _ _ h1 LB1 0 eq_refl eq_refl ltac:(rewrite NNO; reflexivity)
      ltac:(rewrite NH; reflexivity) eq_refl HH). }
  split; [exact NJ1|].
  split; [exact HLAT | exact HBUD].
- (* the rest is over LINE_LIMIT: s->used = 0, s->skip = 1, DI *)
  assert (Hn6 : 6001 <= n).
  { rewrite W_traps.trap_br_ltu in Hc. rewrite (U_atom Ea 25 n E25a) in Hc by lia. rewrite (U_lit Ea 6001) in Hc by lia.
    apply Z.ltb_ge in Hc. exact Hc. }
  clear Hc.
  assert (HBIG : Nat.ltb LINE_LIMIT (length (dW s1) - p) = true).
  { apply Nat.ltb_lt. apply Nat2Z.inj_lt. change (Z.of_nat LINE_LIMIT) with 6000.
    assert (Hz : 6001 <= Z.of_nat (length (dW s1) - p)) by exact Hn6. lia. }
  rewrite HBIG in NU, NSK.
  paj_run_to_tok_xR RUNTOG HS HJ2 SHOK2 dj_Bspan A_dr_top.
  { lazymatch goal with |- awr_ok_x ?E0 ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok_x E0 rs' G XO OUT stk sp0 fp b0 bc ly own) end.
    repeat first [ apply awr_ok_x_nil
      | apply awr_ok_x_cons; [ intros y Hy; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy; rewrite ?B2a, ?B32a in Hy;
          first [ lia | left; split; [right; left; apply FPE; lia | lia] ] | ] ]. }
  lazymatch type of HS with context [restrict _ ?y] => rename y into msF end.
  rename HFr into FR4; rename HG0 into GR4; clear HF.
  assert (KL4 : forall y, 0 <= y < 2 ^ 64 -> ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) (ms_mem msD) y).
  { intros y Hy Hy1 Hy2; apply (aview_eq_of SEGS); apply FR4; rewrite unsigned_lit_small by lia;
    intros (r & Hin & Hr); vm_compute in Hin;
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?B2a, ?B32a in Hr; lia |]); destruct Hin. }
  assert (KPF : forall y, apresent (w_H W1) m1 y -> apresent (w_H W1) (ms_mem msF) y)
    by (intros y Hy; exact (apresent_grows _ _ _ _ GR4 (KPD y Hy))).
  assert (KMF : forall y, 0 <= y < 2 ^ 64 -> ~ (re_buf e1 <= y < re_buf e1 + re_cap e1) ->
    ~ (dxSA cx + 8 <= y < dxSA cx + 12) -> ~ (dxSA cx + 24 <= y < dxSA cx + 32) ->
    ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= y < dsp0 cx - DRAIN_FRAME) ->
    aview SEGS (w_H W1) (ms_mem msF) y = aview SEGS (w_H W1) m1 y)
    by (intros y Hy H1 H2 H3 H4; rewrite KL4 by assumption; apply KMD; assumption).
  assert (HBUFF : garr8 SEGS (arm W1 (ms_mem msF)) (re_buf e1)
    (bzs (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)))).
  { apply (dnk_garr8_kept W1 (ms_mem msD) W1 (ms_mem msF) _ _ HBUFD). intros x Hx. rewrite HLBUF in Hx.
    apply KL4; lia. }
  lazymatch type of HS with
  | st_ok _ ?Ev ?ss _ => pose proof (st_ok_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_region_nth Ev ss _ 2 _ HS eq_refl) as RG2
  | st_ok_pi _ _ ?Ev ?ss _ => pose proof (st_ok_pi_region_nth Ev ss _ 1 _ HS eq_refl) as RG1;
      pose proof (st_ok_pi_region_nth Ev ss _ 2 _ HS eq_refl) as RG2
  end.
  cbn [ms_mem restrict] in RG1, RG2.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 8 4 _ 1 RG1 B32a ltac:(cbn [In]; left; reflexivity)
    ltac:(reflexivity) ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)) as Vs.
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 24 8 _ 0 RG2 B32a ltac:(cbn [In]; left; reflexivity)
    ltac:(reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as Vu.
  pose proof (drr_DMEM_move_xR cx Hp kr ly1 S1 Hp1 W1 m1 (ms_mem msF) md1 _ k1 _ e1 h1 _ out1 ev1 _ LB1
    (dsp0 cx - DRAIN_FRAME - ESTACK) 1 0 [] (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1)) HB HM HJ2 ltac:(unfold ESTACK; lia) ltac:(lia) KMF KPF Vs Vu
    ltac:(lia) ltac:(lia) (eq_refl : Z.of_nat (length ([] : list byte)) = 0) ltac:(lia)
    (ltac:(unfold bzs in HLBUF; rewrite length_map in HLBUF; lia) : Z.of_nat (length (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1))) = re_cap e1 - 0) HBUFF) as HMF.
  pose proof (drr_DMEM_s_xR cx Hp _ _ _ _ _ _ _ _ h1
    (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p)) (dnext (dlive cx) (dxmx cx) s1) out1 ev1 _ LB1
    ltac:(rewrite NNO; reflexivity) ltac:(rewrite NOC; reflexivity) HMF) as HMF2.
  rewrite <- HSENT in HMF2.
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
  prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (20%bv : bv 5) X20.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (24%bv : bv 5) X24.
  prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
  apply Kdi.
  exists (ms_regs msF), ly1, S1, Hp1, (ms_mem msF). eexists. eexists.
  exists (drr_eset e1 1 0 [] (skipn p (re_U e1) ++ skipn (Z.to_nat n) (re_U e1 ++ re_junk e1))), h1, out1, ev1, LB1, spent. eexists. eexists. exists tl.
  split; [reflexivity|].
  split.
  { unfold dregs_top.
    split; [unfold spZ; rewrite X2, (KEPT 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp|].
    split; [rewrite X3, (KEPT 3%nat 3%bv) by (first [lia | reflexivity]); exact R3|].
    split; [rewrite X4, (KEPT 4%nat 4%bv) by (first [lia | reflexivity]); exact R4|].
    split; [rewrite X21, (KEPT 21%nat 21%bv) by (first [lia | reflexivity]); exact R21|].
    split; [rewrite X24, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X20, (KEPT 20%nat 20%bv) by (first [lia | reflexivity]); exact R20|].
    split; [rewrite X22, E32a, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite X27, (KEPT 27%nat 27%bv) by (first [lia | reflexivity]); exact R27|].
    split; [rewrite X8, (KEPT 8%nat 8%bv) by (first [lia | reflexivity]); exact R8|].
    split; [rewrite X9, (KEPT 9%nat 9%bv) by (first [lia | reflexivity]); exact R9|].
    split; [rewrite X18, (KEPT 18%nat 18%bv) by (first [lia | reflexivity]); exact R18|].
    rewrite X26, (KEPT 26%nat 26%bv) by (first [lia | reflexivity]); exact R26. }
  split; [exact HMF2|].
  split; [unfold drr_eset; cbn [re_U]; intros []|].
  split; [unfold drr_eset; cbn [re_used]; unfold APARTIAL; lia|].
  split; [intros _; exact HDB|].
  split.
  { apply (drr_DLINK _ _ e1 _ h1 HL).
    * unfold drr_eset. cbn [re_cap]. rewrite NCAP. pose proof HL as (L1 & _). cbn [dvirt drain_b_c.ds_cap] in L1. exact L1.
    * unfold drr_eset. cbn [re_U]. rewrite NU. reflexivity.
    * unfold drr_eset. cbn [re_skip]. rewrite NSK. reflexivity.
    * unfold drr_eset. cbn [re_keys]. rewrite NH. pose proof HL as (_ & _ & _ & L4 & _). cbn [dvirt drain_b_c.ds_H] in L4. exact L4.
    * unfold drr_eset, drain_b_c.ent_ka. cbn [re_hp re_kh]. rewrite NKA. pose proof HL as (_ & _ & _ & _ & L5 & _).
      cbn [dvirt drain_b_c.ds_ka] in L5. unfold drain_b_c.ent_ka in L5. exact L5.
    * rewrite NEI. reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity. }
  split; [exact HSAME|].
  split.
  { apply (drr_DHIST cx (dvirt cx s1 (dskp s1 p) (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p))
      (dnext (dlive cx) (dxmx cx) s1) _ _ _ _ h1 LB1 0 eq_refl eq_refl ltac:(rewrite NNO; reflexivity)
      ltac:(rewrite NH; reflexivity) eq_refl HH). }
  split; [exact NJ1|].
  split; [exact HLAT | exact HBUD].
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
Lemma drr_DMEM_s_x : forall cx Hp ly S Hp1 (W : world SEGS) m md k e h s s' out ev sent LB,
drain_b_c.ds_no s' = drain_b_c.ds_no s -> drain_b_c.ds_ocap s' = drain_b_c.ds_ocap s ->
DMEM_x B PST ARx RG cx Hp ly S Hp1 W m md k e h s out ev sent LB ->
DMEM_x B PST ARx RG cx Hp ly S Hp1 W m md k e h s' out ev sent LB.
Proof. eapply (drr_DMEM_s_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Lemma drr_DMEM_move_x : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 m2 md1 md2 k1 k2 e1 h1 sg out1 ev1 sent LB1 lo
  sk u U J,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
alloc_ceiling <= lo -> 0 < re_cap e1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (re_buf e1 <= a < re_buf e1 + re_cap e1) -> ~ (dxSA cx + 8 <= a < dxSA cx + 12) ->
  ~ (dxSA cx + 24 <= a < dxSA cx + 32) -> ~ (lo <= a < dsp0 cx - DRAIN_FRAME) ->
  aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m2 a) ->
val_mem SEGS (arm W1 m2) (dxSA cx + 8) 4 sk -> val_mem SEGS (arm W1 m2) (dxSA cx + 24) 8 u ->
(sk = 0 \/ sk = 1) -> 0 <= u -> Z.of_nat (length U) = u -> u <= re_cap e1 ->
Z.of_nat (length J) = re_cap e1 - u -> garr8 SEGS (arm W1 m2) (re_buf e1) (bzs (U ++ J)) ->
DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m2 md2 k2 (drr_eset e1 sk u U J) h1 sg out1 ev1 sent LB1.
Proof. eapply (drr_DMEM_move_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Lemma drr_buf_awr_x : forall cx Hp kr ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 a,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DMEM_x B PST ARx RG cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sg out1 ev1 sent LB1 ->
(re_cap e1 = 8192 \/ re_cap e1 = 16384) -> In (re_buf e1, re_cap e1) (ablocks B ly1 S1) ->
re_buf e1 <= a < re_buf e1 + re_cap e1 ->
(inFP (dFP cx) a /\ exists b nb, In (b, nb) (ablocks B ly1 S1) /\ b <= a < b + req_size nb) \/
in_tmp_block (ablocks B (dxly cx) (dxS cx)) (ablocks B ly1 S1) a.
Proof. eapply (drr_buf_awr_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Theorem dr_rest_x : dr_rest_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (dr_rest_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
End cx.
End b.
End a.
