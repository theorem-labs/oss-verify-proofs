(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SEARCH stage of segment GS of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x837c8 .. 0x8389c, gesture_seen's held-array search, relay.c:100-109 inlined), in the
   form of the cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (a loop over concrete cut states, by
   induction on the iterations left) and lib/A/AC8h.v (call sites), and of this lane's W_send_line_entry.v.
   The statement is lib/A/W_drain_gs.v's gs_scan_stmt, which that file's dr_gs_of consumes; the Section
   header below is W_drain_cx.v's, verbatim.

   GS-SCAN (0x837c8 .. 0x8389c):
     0x837c8-0x837ec  the shadow check of &s->nheld, the load of s->nheld, (&s->held) >> 3, and the test
                      `nheld <= 0`, which goes to 0x83898 (n = 0) and on to GA.
     0x837f0-0x83834  nheld > 0: the shadow check of &s->held, s->held, the callee-saved registers this
                      search clobbers spilled to 8(sp) .. 80(sp), and the loop's registers.
     0x83838-0x83874  the held-key search loop over n: the shadow check of &held[n], strlen (0x83850) and,
                      when the length matches, strncmp (0x83864).  A match leaves at 0x83930, no match in
                      any slot leaves at 0x83878.
     0x83878-0x83894  no match: the registers restored, on to GA (the key is not held).
     0x83930-0x8393c  a match at slot n: the registers restored, then a begin returns to DLN (S q) and an
                      end goes to GF. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx W_drain_gs W_gsscanb_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).

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
(* the instance's laws *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v) *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
(* the allocator's site rules (W_journal.v), at the trampolines the program calls *)
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
(* the allocator instance's granule-tail fact (W_drain_cx.v ALLOC_TAIL) *)
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the callees drain calls as a program *)
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
(* instance facts *)
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
(* placement of the three cells of aout_at that are not in G_DR (W_drain_cx.v HV9 / HV12 / HSM, as
   W_drain_next.v:266-268 and W_drain_pro.v:74-76 take them) *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---------------------------------------------------------------------------------------------------------
   (0) Bytes.  The two interceptors of this stage read their arguments through `aview`; every argument is a
   byte image the cut predicate already carries as a `garr8`, so one bridge serves both.
   --------------------------------------------------------------------------------------------------------- *)

Lemma gss_bz0 : bz (Z_to_bv 8 0) = 0.
Proof. reflexivity. Qed.

Lemma gss_bzs_nth : forall l i, nth i (bzs l) 0 = bz (nth i l (Z_to_bv 8 0)).
Proof.
intros l i. unfold bzs. transitivity (nth i (map bz l) (bz (Z_to_bv 8 0))); [reflexivity|].
apply List.map_nth.
Qed.

Lemma gss_bz_nz : forall b : byte, b <> Z_to_bv 8 0 -> bz b <> 0.
Proof.
intros b Hb E. apply Hb. apply bv_eq. unfold bz in E. rewrite E. reflexivity.
Qed.

Lemma gss_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.

Lemma gss_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

(* a byte of a `garr8` image, as the ASan view reads it *)
Lemma gss_aview_garr8 : forall (W : world SEGS) m base l j,
garr8 SEGS (arm W m) base l -> (j < length l)%nat ->
aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m base l j Hg Hj. destruct (Hg j Hj) as (_ & Hr).
unfold aview. change (mrestrict (w_H W) m) with (arm W m).
rewrite (garr8_mbyte SEGS (arm W m) base l j Hg Hj). cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Hr.
Qed.

(* a window of a byte image *)
Lemma gss_garr8_sub : forall (W : world SEGS) m base l o n,
garr8 SEGS (arm W m) base l -> (o + n <= length l)%nat ->
garr8 SEGS (arm W m) (base + Z.of_nat o) (firstn n (skipn o l)).
Proof.
intros W m base l o n Hg Hon j Hj.
rewrite length_firstn, length_skipn in Hj.
assert (Hj' : (j < n)%nat) by lia.
rewrite nth_firstn, nth_skipn, (proj2 (Nat.ltb_lt j n) Hj').
replace (base + Z.of_nat o + Z.of_nat j) with (base + Z.of_nat (o + j)) by lia.
apply Hg. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (1) The interceptor arguments: `first_byte` of a NUL-terminated key and of the line's prefix, and
   `astrn_agree` as an equality of the two byte lists.
   --------------------------------------------------------------------------------------------------------- *)

Lemma gss_first_byte : forall (W : world SEGS) m base (l : list Z) (n k : Z),
garr8 SEGS (arm W m) base l -> 0 <= k <= n -> n <= Z.of_nat (length l) ->
(forall i, (i < Z.to_nat k)%nat -> nth i l 0 <> 0) ->
(k < n -> nth (Z.to_nat k) l 0 = 0) ->
first_byte SEGS W m base n 0 k.
Proof.
intros W m base l n k Hg Hkn Hnl Hnz Hz. split; [exact Hkn|]. split.
- intros i Hi. exists (nth (Z.to_nat i) l 0). split.
  + replace (base + i) with (base + Z.of_nat (Z.to_nat i)) by lia.
    apply (gss_aview_garr8 W m base l (Z.to_nat i) Hg). lia.
  + apply Hnz. lia.
- intros Hlt. replace (base + k) with (base + Z.of_nat (Z.to_nat k)) by lia.
  rewrite (gss_aview_garr8 W m base l (Z.to_nat k) Hg ltac:(lia)). rewrite (Hz Hlt). reflexivity.
Qed.

Lemma gss_agree_iff : forall (W : world SEGS) m x y (n : Z) (lx ly : list Z),
garr8 SEGS (arm W m) x lx -> garr8 SEGS (arm W m) y ly ->
0 <= n -> n <= Z.of_nat (length lx) -> n <= Z.of_nat (length ly) ->
(forall i, (i < Z.to_nat n)%nat -> nth i lx 0 <> 0) ->
(astrn_agree W m x y n <-> firstn (Z.to_nat n) lx = firstn (Z.to_nat n) ly).
Proof.
intros W m x y n lx ly Hx Hy Hn Hlx Hly Hnz.
assert (AV : forall i, (i < Z.to_nat n)%nat ->
  aview SEGS (w_H W) m (x + Z.of_nat i) = Some (nth i lx 0) /\
  aview SEGS (w_H W) m (y + Z.of_nat i) = Some (nth i ly 0)).
{ intros i Hi. split; [apply (gss_aview_garr8 W m x lx i Hx) | apply (gss_aview_garr8 W m y ly i Hy)]; lia. }
assert (NZ : forall j, 0 <= j < n -> aview SEGS (w_H W) m (x + j) <> Some 0).
{ intros j Hj. replace (x + j) with (x + Z.of_nat (Z.to_nat j)) by lia.
  rewrite (proj1 (AV (Z.to_nat j) ltac:(lia))). intros E. injection E as E.
  exact (Hnz (Z.to_nat j) ltac:(lia) E). }
split.
- intros HA. apply (nth_ext _ _ 0 0).
  { rewrite !length_firstn. lia. }
  intros i Hi. rewrite length_firstn in Hi.
  rewrite !nth_firstn, (proj2 (Nat.ltb_lt i (Z.to_nat n)) ltac:(lia)).
  pose proof (HA (Z.of_nat i) ltac:(lia) ltac:(intros j Hj; apply NZ; lia)) as E.
  rewrite (proj1 (AV i ltac:(lia))), (proj2 (AV i ltac:(lia))) in E.
  injection E as E. exact E.
- intros HE i Hi _. replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia.
  replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (proj1 (AV (Z.to_nat i) ltac:(lia))), (proj2 (AV (Z.to_nat i) ltac:(lia))).
  f_equal.
  assert (Hfi : nth (Z.to_nat i) (firstn (Z.to_nat n) lx) 0 = nth (Z.to_nat i) (firstn (Z.to_nat n) ly) 0)
    by (rewrite HE; reflexivity).
  rewrite !nth_firstn, (proj2 (Nat.ltb_lt (Z.to_nat i) (Z.to_nat n)) ltac:(lia)) in Hfi. exact Hfi.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (2) The two cells of the relay entry the search reads: s->held at + 40 and s->nheld at + 48
   (RelayRep.v:21 entry_bytes).  The proofs are this lane's W_gsbytes_scratch.v:53-166, inlined so that this
   file depends on no other prover's scratch.
   --------------------------------------------------------------------------------------------------------- *)

Lemma gss_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof. intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity. Qed.

Lemma gss_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma gss_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, gss_nth_zle by exact Hk. rewrite gss_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.

Lemma gss_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.

Lemma gss_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H K. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (K x Hx).
Qed.

Lemma gss_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat) by (rewrite gss_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite gss_nth_le_bytes by assumption. reflexivity.
Qed.

Lemma gss_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.

Lemma gss_le4_bytes : forall v, 0 <= v < 2 ^ 32 -> Mem.le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
intros v Hv. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.

Ltac gss_len := rewrite ?length_app, ?gss_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes; cbn [length].

Lemma gss_entry_hp : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_hp e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 40) 8 (re_hp e).
Proof.
intros W m SA e Hp1 Hhp H.
unfold entry_bytes in H. rewrite !gss_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gss_le8_bytes (re_hp e) Hhp) in H.
apply (gss_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hhp|].
apply (gss_garr8_at _ _ _ _ H). gss_len. lia.
Qed.

Lemma gss_entry_nheld : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_nheld e < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 48) 4 (re_nheld e).
Proof.
intros W m SA e Hp1 Hnh H.
unfold entry_bytes in H. rewrite !gss_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gss_le4_bytes (re_nheld e) Hnh) in H.
apply (gss_val_of_garr8 W m _ 4 _); [change (8 * Z.of_nat 4) with 32; exact Hnh|].
apply (gss_garr8_at _ _ _ _ H). gss_len. lia.
Qed.

(* slot n of the held array, from the array's byte image (gestures_end_b_c.v:29 key_ptrs) *)
Lemma gss_slot_val : forall (W : world SEGS) m hp (ks : list (Z * list byte * list byte)) (n : nat),
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) -> (n < length ks)%nat ->
0 <= key_addr (nth n ks (0, [], [])) < 2 ^ 64 ->
val_mem SEGS (arm W m) (hp + 8 * Z.of_nat n) 8 (key_addr (nth n ks (0, [], []))).
Proof.
intros W m hp ks n Hg Hn Hk.
destruct (nth_split ks (0, [], []) Hn) as (a & b & E & Ha).
set (x := nth n ks (0, [], [])) in *. clearbody x. subst ks n.
rewrite gsx_key_ptrs_cat, gsx_key_ptrs_cons, !gss_bzs_app in Hg.
apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
rewrite (gss_le8_bytes (key_addr x) Hk) in Hg.
apply (gss_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hk|].
apply (gss_garr8_at _ _ _ _ Hg). rewrite gss_bzs_len, gs_key_ptrs_len. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (3) The symbolic state at DGS (0x837c8).
   Atoms beyond the 32 registers: 32 = SA (the relay entry), 33 = s->held, 34 = s->nheld.  The shadow base is
   register atom 21 (dregs_line pins s5 = SHADOW_OFF), so Bx is SOff 21 0 and the two shadow checks of this
   stage (&s->nheld at SA + 48, &s->held at SA + 40) are the `srli; add s5; lb` form tok_load folds against
   the single entry mkSHE 32 40 56.  The frame is split into the two windows this stage writes
   (8(sp)..40(sp) and 72(sp), 80(sp)) and the two it only reads (48(sp), 56(sp) and 96(sp), 128(sp)).
   --------------------------------------------------------------------------------------------------------- *)

Definition GS_PHI : Z := 140737479966720.
Definition GSBx : sv := SOff 21 0.
Definition GS_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

Definition gse_frameW : YP09.region := YP09.mkRegion (Some 2%nat) 0 48 0 48 [].
Definition gse_frameR : YP09.region := YP09.mkRegion (Some 2%nat) 48 64 0 0
  [ YP09.mkChunk 48 (CVal 8 (SOff 32 24)); YP09.mkChunk 56 (CVal 8 (SOff 32 0)) ].
Definition gse_frameW2 : YP09.region := YP09.mkRegion (Some 2%nat) 72 88 72 88 [].
Definition gse_frameR2 : YP09.region := YP09.mkRegion (Some 2%nat) 96 136 0 0
  [ YP09.mkChunk 96 (CVal 8 (SOff 32 48)); YP09.mkChunk 128 (CVal 8 (SOff 32 40)) ].
Definition gse_ent : YP09.region := YP09.mkRegion (Some 32%nat) 40 52 0 0
  [ YP09.mkChunk 40 (CVal 8 (SOff 33 0)); YP09.mkChunk 48 (CVal 4 (SOff 34 0)) ].
Definition gse_regions : smem := [ gse_frameW; gse_frameR; gse_frameW2; gse_frameR2; gse_ent ].
Definition gse_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF SB SB 0);
          (32%nat, mkAF 4096 GS_PHI 0); (33%nat, mkAF 0 GS_PHI 0); (34%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_gse : sstate := mkSS A_dr_seen sr_atoms gse_regions None gse_facts.
Definition gse_SH : list shent := [ mkSHE 32 40 56 ].
Definition gse_extra (SA HP NH : Z) : list word := map (Z_to_bv 64) [SA; HP; NH].

Lemma gse_entry : forall (W : world SEGS) regs1 m1 sp SA HP NH,
spZ regs1 = sp -> 2 ^ 46 <= sp -> sp + DRAIN_FRAME <= 2 ^ 47 -> sp mod 16 = 0 ->
getr regs1 21 = w64 SHADOW_OFF ->
4096 <= SA -> SA + 56 <= GS_PHI -> SA + 56 <= sp ->
0 <= HP <= GS_PHI -> 0 <= NH < 2 ^ 26 ->
(forall o, 0 <= o < 48 -> writable_at SEGS (arm W m1) (sp + o)) ->
(forall o, 72 <= o < 88 -> writable_at SEGS (arm W m1) (sp + o)) ->
val_mem SEGS (arm W m1) (sp + 48) 8 (SA + 24) ->
val_mem SEGS (arm W m1) (sp + 56) 8 SA ->
val_mem SEGS (arm W m1) (sp + 96) 8 (SA + 48) ->
val_mem SEGS (arm W m1) (sp + 128) 8 (SA + 40) ->
val_mem SEGS (arm W m1) (SA + 40) 8 HP ->
val_mem SEGS (arm W m1) (SA + 48) 4 NH ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (gse_extra SA HP NH))) ss_gse
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_seen)) m1 (seg_rom SEGS))).
Proof.
intros W regs1 m1 sp SA HP NH Hsp Hlo Hhi Hal R21 HSA1 HSA2 HSA3 HHP HNH WR1 WR2 M48 M56 M96 M128 MHP MNH.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (gse_extra SA HP NH))).
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 HP) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 NH) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (Usa : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; unfold GS_PHI in *; lia).
unfold GS_PHI in HSA2, HHP. unfold DRAIN_FRAME in Hhi.
unfold ss_gse. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold gse_regions, gse_frameW, gse_frameR, gse_frameW2, gse_frameR2, gse_ent.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?Usp, ?Usa.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; exact (WR1 o Ho) | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp 48 8 (SOff 32 24) (SA + 24));
      [rewrite (den_atom E 32%nat SA 24 E32) by lia; reflexivity | cbn; lia | cbn; lia | exact M48].
    * apply (chunk_ok_val SEGS E _ sp 56 8 (SOff 32 0) SA);
      [rewrite (den_atom0 E 32%nat SA E32) by lia; reflexivity | cbn; lia | cbn; lia | exact M56].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; exact (WR2 o Ho) | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp 96 8 (SOff 32 48) (SA + 48));
      [rewrite (den_atom E 32%nat SA 48 E32) by lia; reflexivity | cbn; lia | cbn; lia | exact M96].
    * apply (chunk_ok_val SEGS E _ sp 128 8 (SOff 32 40) (SA + 40));
      [rewrite (den_atom E 32%nat SA 40 E32) by lia; reflexivity | cbn; lia | cbn; lia | exact M128].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ SA 40 8 (SOff 33 0) HP);
      [rewrite (den_atom0 E 33%nat HP E33) by lia; reflexivity | cbn; lia | cbn; lia | exact MHP].
    * apply (chunk_ok_val SEGS E _ SA 48 4 (SOff 34 0) NH);
      [rewrite (den_atom0 E 34%nat NH E34) by lia; reflexivity | cbn; lia | cbn; lia | exact MNH].
- apply pairwise_disjoint_of_extents.
  unfold gse_regions, gse_frameW, gse_frameR, gse_frameW2, gse_frameR2, gse_ent, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Usa.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [gse_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Usa, E21, E33, E34, !unsigned_lit_small by (unfold SB, SHADOW_OFF; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, SHADOW_OFF, GS_PHI. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (3a) Lowness: every byte the cut's representations touch lies below the allocator ceiling, far below the
   frame this stage writes.  (W_drain_pro.v:208-408's pro_*_fp_low, at aentry_okx's slack-free key clause.)
   --------------------------------------------------------------------------------------------------------- *)

Lemma gss_blk_low : forall ly S (W : world SEGS) mem md qq nn a,
AR SEGS B ly S W mem md -> In (qq, nn) (ablocks B ly S) -> qq <= a -> a < qq + req_size nn ->
0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md qq nn a HAR Hin H1 H2.
destruct (al_blocks SEGS B LAWS ly S W mem md qq nn HAR Hin) as (_ & H4096 & Hceil & _). lia.
Qed.

Lemma gss_img_low : forall a lo hi, 0x10000 <= lo -> lo <= a -> a < hi -> hi <= 0x5fb000 ->
0 <= a < alloc_ceiling.
Proof. intros a lo hi H1 H2 H3 H4. pose proof asan_consts as (C1 & _). lia. Qed.

Lemma gss_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma gss_aentry_fp_low : forall ly S (W : world SEGS) mem md e,
AR SEGS B ly S W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (HPK : forall k, In k (re_keys e) ->
  key_addr k <= a < key_addr k + Z.of_nat (length (bzs (key_text k ++ [Z_to_bv 8 0]))) ->
  0 <= a < alloc_ceiling).
{ intros k Hk Hak. rewrite gss_bzs_len, length_app in Hak. cbn [length] in Hak.
  rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
  apply (gss_blk_low ly S W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR Hin); [lia|].
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia. }
assert (HPH : re_hp e <= a < re_hp e + Z.of_nat (length (bzs (key_ptrs (re_keys e)))) ->
  0 <= a < alloc_ceiling).
{ intros Hah. rewrite gss_bzs_len, gs_key_ptrs_len in Hah.
  destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
  - rewrite Hke in Hah. cbn [length] in Hah. lia.
  - apply (gss_blk_low ly S W mem md (re_hp e) (re_kh e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq). unfold re_nheld in Hk1. lia. }
unfold aentry_fp in Hr.
destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [app In] in Hr.
- destruct Hr as [<- | Hr]; [unfold gfp in Ha; cbn [fst snd] in Ha; exact (HPH Ha)|].
  apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
- destruct Hr as [<- | [<- | Hr]].
  + unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gss_bzs_len, length_app in Ha.
    destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gss_blk_low ly S W mem md (re_buf e) (re_cap e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia.
  + unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPH Ha).
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
Qed.

Lemma gss_alist_fp_low : forall ly S (W : world SEGS) mem md LA l lines lo hi,
AR SEGS B ly S W mem md -> alist_at B ly S W mem LA l lines ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= 0x5fb000 ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md LA l lines lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (gss_img_low a lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gss_bzs_len, length_app, gss_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gss_blk_low ly S W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n, AREC in *. lia.
  + apply in_map_iff in Hr as (qq & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gss_bzs_len, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs qq Hq) as (Hin & _).
    apply (gss_blk_low ly S W mem md (fst qq) (Z.of_nat (length (snd qq)) + 1) a HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd qq)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma gss_asrc_fp_low : forall ly S (W : world SEGS) mem md HA h,
AR SEGS B ly S W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (gss_img_low a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gss_bzs_len in Ha.
  apply (gss_blk_low ly S W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- unfold ASRC in *. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + eapply (gss_alist_fp_low ly S W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * 96));
      [exact HAR | exact Hpend | lia | lia | lia | lia | exact Hr | exact Ha].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * eapply (gss_alist_fp_low ly S W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hexp | lia | lia | lia | lia | exact Hr | exact Ha].
    * eapply (gss_alist_fp_low ly S W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hheld | lia | lia | lia | lia | exact Hr | exact Ha].
Qed.

Ltac gss_ing := unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma gss_aout_fp_low : forall ly S (W : world SEGS) mem md c O mx no cap out,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof asan_consts as (C1 & _).
assert (GL2 : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> 0 <= a < alloc_ceiling).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (pa_img_range _ (proj1 (HG a HI))). lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (gss_img_low a (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL2 (rg_nout RG) 8); [gss_ing | lia].
- apply (GL2 (rg_capout RG) 8); [gss_ing | lia].
- apply (GL2 (rg_out RG) 8); [gss_ing | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (gss_img_low a (rg_client RG) (rg_client RG + 4)); lia.
- apply (GL2 (rg_client_broken RG) 1); [gss_ing | lia].
- pose proof (pa_obj_img 12 ltac:(lia)) as H12. rewrite HV12 in H12.
  apply (gss_img_low a (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL2 (rg_send_eintr RG) 1); [gss_ing | lia].
- apply (GL2 (as_errno B) 4); [gss_ing | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (gss_blk_low ly S W mem md out cap a HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

(* a value read off memory survives a step that keeps its bytes' view *)
Lemma gss_vm_keep : forall (W : world SEGS) m m' a (n : nat) v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v.
Proof.
intros W m m' a n v K H k Hk. unfold arm.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' (a + Z.of_nat k) (K (a + Z.of_nat k) ltac:(lia))).
exact (H k Hk).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (3b) The cut survives the stage.  This stage writes only 8(sp) .. 40(sp) and 72(sp), 80(sp) of its own
   frame, and the two interceptors write only their scratch below sp; so every byte outside
   [sp0 - DRAIN_FRAME, sp0 - DRAIN_FRAME + 88) keeps its view and presence only grows, and the line loop's
   core moves to the new memory unchanged.
   --------------------------------------------------------------------------------------------------------- *)
Lemma gss_core_kept : forall cx s1 D p q ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  m2 md2 k2,
alloc_ceiling + 88 <= dsp0 cx - DRAIN_FRAME -> dsp0 cx <= 2 ^ 47 -> (dxj cx < 4)%nat ->
4096 <= dxSA cx -> dxSA cx + 56 <= alloc_ceiling ->
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k2 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME <= x < dsp0 cx - DRAIN_FRAME + 88) ->
   aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m2 x) ->
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m2 md2 k2 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 k2 HLOW HTOP HJ4 HSA1 HSA2 HGS HJ2 KEEP PRES.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold GSB, LCORE in HGS |- *.
destruct HGS as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR1 : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (KL : forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x)
  by (intros x Hx; apply KEEP; lia).
assert (KF : forall x, dsp0 cx - DRAIN_FRAME + 88 <= x < dsp0 cx -> aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x)
  by (intros x Hx; apply KEEP; unfold DRAIN_FRAME in *; lia).
assert (AK : forall fp, (forall r, In r fp -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling) ->
  akept W1 m1 W1 m2 fp) by (intros fp Hlow; exact (gs_akept_of W1 m1 m2 fp KL PRES Hlow)).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (HBLK : forall b, In b (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap
    (dvirt cx s1 false (dlH cx s1 p) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q))) out1) ->
  In b (ablocks B ly1 S1)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact Hperm | right].
  apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb|right].
  apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb|right].
  apply in_or_app. left. exact Hb. }
split; [|split; [exact HLINK | split; [exact HSAME | split; [exact HHIST | split; [exact HRS | exact HBUD]]]]].
split; [exact HJ2|].
split.
{ intros x Hx. rewrite KL; [exact (Hrom x Hx)|].
  destruct Hx as (sg & Hsg & _ & Hr).
  pose proof (pa_img_range x ltac:(exists sg; split; [exact Hsg | exact Hr])). lia. }
split; [intros x Him Hno Her Hp; exact (PRES x (Hpres x Him Hno Her Hp))|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224 & F216 & F176 & Hsvd).
  repeat split;
    try (apply (gss_vm_keep W1 m1 m2 _ 8%nat _);
         [intros x Hx; apply KF; unfold DRAIN_FRAME in *; lia | assumption]).
  intros i Hi. apply (gss_vm_keep W1 m1 m2 _ 8%nat _);
    [intros x Hx; apply KF; unfold DRAIN_FRAME in *; lia | exact (Hsvd i Hi)]. }
(* the relay entry's 56 bytes lie in the table block *)
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR1 HTB) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.

split.
{ apply (gss_garr8_kept W1 m1 W1 m2); [exact Hgarr|].
  intros x Hx. rewrite gss_bzs_len in Hx. apply KL.
  assert (HL56 : length (entry_bytes e1) = 56%nat).
  { pose proof HOKX as (_ & _ & Hp1 & Hp2 & _). unfold entry_bytes.
    rewrite !length_app, Hp1, Hp2, !Mem.length_le8, !Mem.length_le4. reflexivity. }
  rewrite HL56 in Hx. unfold ATABLE, AENT in *. lia. }
split.
{ intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hawr i Hi). }
split.
{ eapply (gs_aentry_okx_kept B RG).
  - exact HOKX.
  - apply AK. exact (gss_aentry_fp_low ly1 S1 W1 m1 md1 e1 HAR1 HOKX).
  - intros b Hb. apply HBLK. apply in_or_app. left. exact Hb. }
split.
{ eapply asrc_at_kept.
  - exact Hsrc.
  - apply AK. apply (gss_asrc_fp_low ly1 S1 W1 m1 md1 (dHA RG cx) h1 HAR1 Hsrc);
      unfold dHA, ASRC in *; lia.
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split.
{ pose proof HGSB as (Hg1 & Hg2 & _). unfold aothers_at in Hoth |- *.
  intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & Mf & Mo & Hfo).
  exists f, o. split; [|split; [|exact Hfo]];
  apply (gss_vm_keep W1 m1 m2 _ 4%nat _); [| exact Mf | | exact Mo];
  intros x Hx; apply KL; apply (gss_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia. }
split.
{ intros x Hx Hnx. destruct (Hgsk x Hx Hnx) as (Hv & Hw). split.
  - rewrite KL; [exact Hv|]. pose proof HGSB as (Hg1 & Hg2 & _).
    apply (gss_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
  - intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hw Hwr). }
split.
{ eapply aout_at_kept.
  - exact Hout.
  - apply AK. exact (gss_aout_fp_low ly1 S1 W1 m1 md1 _ _ _ _ _ _ HAR1 Hout).
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. right. exact Hb. }
split; [exact Hlivout | exact Hperm].
Qed.


(* ---- the symbolic values this stage reads, and its one signed branch (blez on s->nheld) ---- *)
Lemma gss_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma gss_U_srl : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma gss_U_shadow : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 21 0)) = (v + c) / 8 + SHADOW_OFF.
Proof.
intros E n v c Hn H21 Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (gss_U_srl E n v c Hn Hv Hc), (U_atom E 21 SHADOW_OFF H21) by (unfold SHADOW_OFF; lia).
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61) by
  (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma gss_U_shadow2 : forall E n v, ew E n = Z_to_bv 64 v -> ew E 21 = Z_to_bv 64 SHADOW_OFF ->
0 <= v < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff 21 0) (SAlu ALU_SRL (SOff n 0) (SLit 3))) = v / 8 + SHADOW_OFF.
Proof.
intros E n v Hn H21 Hv. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 21 SHADOW_OFF H21) by (unfold SHADOW_OFF; lia).
rewrite (gss_U_srl E n v 0 Hn Hv ltac:(lia)), Z.add_0_r.
assert (Hd : 0 <= v / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

Lemma gss_U_sll3 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v -> 8 * v < 2 ^ 64 ->
U E (SAlu ALU_SLL (SOff n 0) (SLit 3)) = 8 * v.
Proof.
intros E n v Hn Hv Hv8. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n v Hn) by lia. rewrite U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma gss_U_sub : forall E m n vm vn,
ew E m = Z_to_bv 64 vm -> ew E n = Z_to_bv 64 vn ->
0 <= vm -> vm <= vn -> vn < 2 ^ 63 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff m 0) (SLit (-1))) (SOff n 0)) = vn - vm.
Proof.
intros E m n vm vn Hm Hn Hm0 Hmn Hn63.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E m vm Hm) by lia. rewrite (U_atom E n vn Hn) by lia. rewrite U_SLit.
unfold zcanon, M64.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (vm * (2 ^ 64 - 1)) with (- vm + vm * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, Zplus_mod_idemp_l.
replace (- vm + vn) with (vn - vm) by ring.
apply Z.mod_small. lia.
Qed.

Lemma gss_shadow_range : forall v, 0 <= v < 2 ^ 63 -> 0 <= v / 8 + SHADOW_OFF < 2 ^ 64.
Proof.
intros v Hv. pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia.
Qed.

Lemma gss_srl3_lit : forall v, 0 <= v < 2 ^ 64 ->
alu64 ALU_SRL (Z_to_bv 64 v) (Z_to_bv 64 3) = Z_to_bv 64 (v / 8).
Proof.
intros v Hv.
assert (Hv8 : 0 <= v / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hv8.
Qed.

Lemma gss_lts_lit : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
intros x y Hx Hy.
assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply unsigned_lit_small; lia).
assert (Uy : bv_unsigned (Z_to_bv 64 y) = y) by (apply unsigned_lit_small; lia).
rewrite bv_lts_signed.
rewrite (signed_of_small (Z_to_bv 64 x)) by (rewrite Ux; unfold half64; lia).
rewrite (signed_of_small (Z_to_bv 64 y)) by (rewrite Uy; unfold half64; lia).
rewrite Ux, Uy. reflexivity.
Qed.

(* the registers the whole search leaves alone *)
Definition GS_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 21; 23; 24]%bv.
(* arm 1 (nheld <= 0) runs only `li a0, 0`, so it keeps the search's registers too *)
Definition GS_KEPT1 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 27]%bv.

(* a register's abstract value, without prreg's normalisation of sv_denot *)
Ltac gss_rreg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?Ev ?ssv (restrict ?H ?msv) =>
  pose proof (st_ok_pi_restrict_reg H Ev ssv msv r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ssv) r) in
  change (sr_get (ss_regs ssv) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* an address outside [sp, sp + 88) is outside every write window of this stage's runs *)
Ltac gss_in := cbn [In]; repeat first [left; reflexivity | right].

Ltac gss_nowr Usp :=
  let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (rr & Hin & Hr); cbn [ss_mem add_cond add_atom In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr;
      unfold DRAIN_FRAME in *; lia |]);
  destruct Hin.

(* The write obligation of a run of this stage: the regions are the frame's two write windows (8(sp) .. 40(sp)
   and 72(sp), 80(sp), both inside [sp0 - DRAIN_STK, sp0)) and read-only regions. *)
Ltac gss_awr Usp :=
  apply awr_ok_x_of0; awr_ok_tac;
  repeat (eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- DRAIN_FRAME));
          [ reflexivity
          | rewrite Usp; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_wlo]; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_whi]; unfold DRAIN_FRAME; lia
          | awr_ok_tac ]).

(* The stage, given the held-search loop (lib/A/W_gsscanb_cx.v gs_scan_loop_stmt). *)
Theorem gs_scan_of_loop : gs_scan_loop_stmt B MT MMAX RG -> gs_scan_stmt B MT MMAX RG.
Proof.
intros LOOP.
unfold gs_scan_stmt. intros cx s1 D p q W1 c1 HB HGS HDLN HGA HGF.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK = 16848) by reflexivity.
unfold DGS in HGS.
destruct HGS as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks & tl
  & kd & jj & bg & Hcfg & Hregs & H23 & H24 & H25 & H19 & Hbgr & Hbgk & Hgest & Hjjr
  & Hbd & Hpq & Hq0 & Hnz & Hskp & Hlim & HLC & HFUT).
pose proof Hregs as (Hsp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64).
pose proof HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224 & F216 & F176 & Hsaved).
pose proof HLC as HLC'. unfold LCORE in HLC'.
destruct HLC' as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpresk & Hframes & _ & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (Hafn & HBx10 & Htbl & HSAlo & HSAhi & Hgarr0 & Hawr0 & Hent0 & HJ4 & HBrest).
pose proof Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
fold (dsp0 cx) in Hal16, Hslo, Hshi, Htop1.
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (HG16 & HG4096 & HGceil & HGia & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
unfold ATABLE, AENT in *.
pose proof HOKX as (Heof & Hskipe & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & HND1 & HND2 & Hkeys).
(* the journal's stack: the frame is present, hence writable *)
pose proof HJ as (HSTKj & HXOj & (memS & HJi & HAGj) & HOUTj).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRESj & _).
assert (WRF : forall x, dsp0 cx - DRAIN_STK <= x < dsp0 cx -> writable_at SEGS (arm W1 m1) x)
  by (intros x Hx; apply (apresent_writable SEGS); apply HPRESj; lia).
(* the two cells the search reads off the relay entry *)
assert (HHPR : 0 <= re_hp e1 <= GS_PHI).
{ destruct Hheld as [(Hz & _)|(Hz & Hin & Hk1 & Hk2 & _)]; [unfold GS_PHI; lia|].
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (_ & H4 & Hc & _).
  pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (Hr1 & Hr2). unfold GS_PHI. lia. }
assert (HNHR : 0 <= re_nheld e1 < 2 ^ 26) by (split; [unfold re_nheld; lia | exact Hnheld]).
pose proof (gss_entry_hp W1 m1 (dxSA cx) e1 Hpad1 ltac:(unfold GS_PHI in HHPR; lia) Hgarr) as MHP.
pose proof (gss_entry_nheld W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MNH.
(* the symbolic state at 0x837c8 *)
pose proof (gse_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_hp e1) (re_nheld e1)
  Hsp ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity) R21
  ltac:(lia) ltac:(unfold GS_PHI; lia) ltac:(lia) HHPR HNHR
  ltac:(intros o Ho; apply WRF; lia) ltac:(intros o Ho; apply WRF; lia)
  M48 M56 F96 F128 MHP MNH) as HS.
remember (Eimg (Ereg regs1 (gse_extra (dxSA cx) (re_hp e1) (re_nheld e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (gse_extra (dxSA cx) (re_hp e1) (re_nheld e1))) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EREG 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_hp e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_nheld e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (HBx : U E GSBx = SHADOW_OFF)
  by (unfold GSBx; rewrite (U_atom E 21 SHADOW_OFF E21) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS GSBx gse_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E GSBx 32 (dxG cx) 896 (dxSA cx) 40 56).
  - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) 896); [exact HAR | exact HTB | lia | rewrite RQT; lia].
  - exact HBx.
  - apply (U_atom E 32 (dxSA cx) E32). unfold GS_PHI in *. lia.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. rewrite RQT in HGia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_seen)) with (Z_to_bv 64 (BASE + A_dr_seen)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
paj_run_tok RUN HS HJ SHOK GS_Bspan. { gss_awr Usp. }
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hg into GR1 end.
(* the run to the nheld test wrote only 72(sp) *)
assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME <= x < dsp0 cx - DRAIN_FRAME + 48) ->
  ~ (dsp0 cx - DRAIN_FRAME + 72 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
  aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno Hno'. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr x Hx).
  intros (r & Hin & Hr). cbn [ss_mem ss_gse gse_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi gse_frameW gse_frameR gse_frameW2 gse_frameR2 gse_ent base_val] in Hr;
  rewrite ?Usp in Hr; unfold DRAIN_FRAME in *; lia. }
assert (PRES1 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR1 Hp)).
clear HF HFr GR1.
psrr_branch_tok RUN BR HS SHOK GS_Bspan.
-
(* nheld <= 0: nothing is held, so the key is not held; n = 0 at 0x83898, on to GA. *)
unfold branch_taken in Hc. cbn [sv_denot] in Hc.
rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
rewrite (gss_lts_lit 0 (re_nheld e1) ltac:(lia) ltac:(lia)) in Hc.
apply Bool.negb_true_iff, Z.ltb_ge in Hc.
assert (HN0 : re_nheld e1 = 0) by lia.
assert (HKE : re_keys e1 = []) by (apply length_zero_iff_nil; unfold re_nheld in HN0; lia).
paj_run_to_tok RUNTO HS HJ SHOK GS_Bspan A_dr_add. { gss_awr Usp. }
match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem ms0)) |- _ =>
  rename Hg into GR2 end.
assert (KEEP2 : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME <= x < dsp0 cx - DRAIN_FRAME + 48) ->
  ~ (dsp0 cx - DRAIN_FRAME + 72 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
  aview SEGS (w_H W1) (ms_mem ms0) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno Hno'. rewrite <- (KEEP1 x Hx Hno Hno').
  apply (aview_kept_out E _ (w_H W1) (ms_mem ms) (ms_mem ms0) HFr x Hx). gss_nowr Usp. }
assert (PRES2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms0) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR2 (PRES1 x Hp))).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ GS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (27%bv : bv 5) Q27.
(* the shadow slot the stage wrote at 72(sp) *)
assert (M72 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 72) 8
               ((dxSA cx + 48) / 8 + SHADOW_OFF)).
{ lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
    pose proof (st_ok_pi_region_nth Ev ssv msv 2 _ HS eq_refl) as HR72 end.
  cbn [ms_mem restrict] in HR72.
  apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 72 88 72 88 72
           (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 48) (SLit 3)) (SOff 21 0)) _ HR72 Usp
           ltac:(cbn [In]; left; reflexivity));
  [ apply gss_den; apply (gss_U_shadow E 32 (dxSA cx) 48 E32 E21); unfold GS_PHI in *; lia
  | pose proof (Z.div_pos (dxSA cx + 48) 8 ltac:(lia) ltac:(lia));
    pose proof (Z.div_lt_upper_bound (dxSA cx + 48) 8 (2 ^ 61) ltac:(lia) ltac:(unfold GS_PHI in *; lia));
    unfold SHADOW_OFF; lia ]. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ GS_KEPT1 HS HAE ltac:(vm_compute; reflexivity)) as HK1.
cbn [ms_regs restrict] in HK1.
assert (FR2 : dr_frame RG cx W1 (ms_mem ms0)).
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (G208 & G96 & G128 & G88 & G184 & G120 & G112 & G104 & G144 & G152 & G168 & G136 & G160 & G224 & G216 & G176 & Gsvd).
  repeat split;
    try (apply (gss_vm_keep W1 m1 (ms_mem ms0) _ 8%nat _);
         [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | assumption]).
  intros i Hi. apply (gss_vm_keep W1 m1 (ms_mem ms0) _ 8%nat _);
    [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact (Gsvd i Hi)]. }
assert (HdlH : dlH cx s1 p = []).
{ destruct HLINK as (_ & _ & _ & HKT & _). unfold dvirt in HKT. cbn [drain_b_c.ds_H] in HKT.
  rewrite <- HKT, HKE. reflexivity. }
pmkst HS.
apply HGA. unfold GA.
exists (ms_regs ms0), ly1, S1, (ms_mem ms0). eexists. eexists.
exists e1, h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl, kd, jj, bg.
split; [unfold cfg_at; reflexivity|].
split.
{ unfold dregs_line.
  split; [unfold spZ; rewrite (HK1 2%bv ltac:(cbv; tauto)); exact Hsp|].
  split; [rewrite (HK1 3%bv ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (HK1 4%bv ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (HK1 22%bv ltac:(cbv; tauto)); exact R22|].
  split; [rewrite (HK1 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [rewrite (HK1 18%bv ltac:(cbv; tauto)); exact R18|].
  split; [rewrite (HK1 9%bv ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (HK1 8%bv ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (HK1 21%bv ltac:(cbv; tauto)); exact R21|].
  split; [exact FR2|].
  repeat split; apply (gss_vm_keep W1 m1 (ms_mem ms0) _ 8%nat _);
    first [ intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | assumption ]. }
split; [rewrite (HK1 23%bv ltac:(cbv; tauto)); exact H23|].
split; [rewrite (HK1 24%bv ltac:(cbv; tauto)); exact H24|].
split; [rewrite (HK1 25%bv ltac:(cbv; tauto)); exact H25|].
split; [rewrite (HK1 19%bv ltac:(cbv; tauto)); exact H19|].
split; [rewrite Q10, HN0; reflexivity|].
split; [rewrite Q11, E34; reflexivity|].
split; [rewrite Q12, E32, (unsigned_lit_small (dxSA cx)) by (unfold GS_PHI in *; lia);
  rewrite gss_srl3_lit by (unfold GS_PHI in *; lia); reflexivity|].
split; [exact M72|].
split; [exact Hbgr|]. split; [exact Hbgk|]. split; [exact Hgest|]. split; [exact Hjjr|].
split; [rewrite HdlH; reflexivity|].
split; [unfold GSF; split; [exact Hbd|]; split; [exact Hpq|]; split; [exact Hq0|];
  split; [exact Hnz|]; split; [exact Hskp | exact Hlim]|].
split; [|exact HFUT].
apply (gss_core_kept cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl _ _ _
  ltac:(unfold DRAIN_FRAME, DRAIN_STK in *; lia) ltac:(lia) HJ4 ltac:(lia) ltac:(lia) HLC HJ
  ltac:(intros x Hx Hno; apply KEEP2; [exact Hx | unfold DRAIN_FRAME in *; lia | unfold DRAIN_FRAME in *; lia])
  PRES2).
-
(* nheld > 0: the shadow check of &s->held, the spills, and the loop's registers, to 0x83838 with n = 0. *)
unfold branch_taken in Hc. cbn [sv_denot] in Hc.
rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
rewrite (gss_lts_lit 0 (re_nheld e1) ltac:(lia) ltac:(lia)) in Hc.
apply Bool.negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_tok RUNTO HS HJ SHOK GS_Bspan A_dr_hloop. { gss_awr Usp. }
gss_rreg HS (19%bv : bv 5) P19. gss_rreg HS (20%bv : bv 5) P20.
gss_rreg HS (25%bv : bv 5) P25. gss_rreg HS (27%bv : bv 5) P27.
match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem ms0)) |- _ =>
  rename Hg into GR2 end.
assert (KEEP2 : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME <= x < dsp0 cx - DRAIN_FRAME + 48) ->
  ~ (dsp0 cx - DRAIN_FRAME + 72 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
  aview SEGS (w_H W1) (ms_mem ms0) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno Hno'. rewrite <- (KEEP1 x Hx Hno Hno').
  apply (aview_kept_out E _ (w_H W1) (ms_mem ms) (ms_mem ms0) HFr x Hx). gss_nowr Usp. }
assert (PRES2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms0) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR2 (PRES1 x Hp))).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ GS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
(* the line lies in the relay's buffer, so every address the loop's registers hold is small *)
assert (HUW : bzs (re_U e1) = dW s1)
  by (destruct HLINK as (_ & HU & _); unfold dvirt in HU; cbn [drain_b_c.ds_u] in HU; exact HU).
assert (HWlen : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HUW, gss_bzs_len; exact HUlen).
assert (HBUF : In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\ 0 < re_cap e1).
{ destruct Hbufc as [(Hc0 & Hb0 & Hu0)|(Hcpos & Hbin & Hjunk & Hbuf8)]; [exfalso; lia | split; assumption]. }
destruct HBUF as (HBin & HBcap).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR HBin)
  as (_ & HB4096 & HBceil & _).
assert (RQB : req_size (re_cap e1) = re_cap e1)
  by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQB in HBceil.
assert (HLINE : 0 <= re_buf e1 + Z.of_nat p /\ re_buf e1 + Z.of_nat p + Z.of_nat jj < 2 ^ 63).
{ split; [lia|]. assert (Z.of_nat q < re_used e1) by lia. lia. }
destruct HLINE as (HL1 & HL2).
assert (E24' : ew E 24 = Z_to_bv 64 (re_buf e1 + Z.of_nat p))
  by (rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl); exact H24).
assert (E25' : ew E 25 = Z_to_bv 64 (re_buf e1 + Z.of_nat p + Z.of_nat jj))
  by (rewrite (EREG 25%nat 25%bv ltac:(lia) eq_refl); exact H25).
assert (E19' : ew E 19 = Z_to_bv 64 bg) by (rewrite (EREG 19%nat 19%bv ltac:(lia) eq_refl); exact H19).
(* the seven frame slots the setup wrote *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_region_nth Ev ssv msv 0 _ HS eq_refl) as HR0;
  pose proof (st_ok_pi_region_nth Ev ssv msv 2 _ HS eq_refl) as HR2 end.
cbn [ms_mem restrict] in HR0, HR2.
assert (N8 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 8) 8
             ((dxSA cx + 40) / 8 + SHADOW_OFF)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 48 0 48 8
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 40) (SLit 3)) (SOff 21 0)) _ HR0 Usp ltac:(gss_in));
  [ apply gss_den; apply (gss_U_shadow E 32 (dxSA cx) 40 E32 E21); unfold GS_PHI in *; lia
  | apply gss_shadow_range; unfold GS_PHI in *; lia ]. }
assert (N16 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 40) / 8)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 48 0 48 16
    (SAlu ALU_SRL (SOff 32 40) (SLit 3)) _ HR0 Usp ltac:(gss_in));
  [ apply gss_den; apply (gss_U_srl E 32 (dxSA cx) 40 E32); unfold GS_PHI in *; lia
  | pose proof (Z.div_pos (dxSA cx + 40) 8 ltac:(lia) ltac:(lia));
    pose proof (Z.div_lt_upper_bound (dxSA cx + 40) 8 (2 ^ 60) ltac:(lia) ltac:(unfold GS_PHI in *; lia));
    lia ]. }
assert (N24 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 24) 8 (re_nheld e1)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 48 0 48 24 (SOff 34 0) _ HR0 Usp ltac:(gss_in));
  [ apply (den_atom0 E 34%nat (re_nheld e1) E34); lia | lia ]. }
assert (N32 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 32) 8
              (re_buf e1 + Z.of_nat p + Z.of_nat jj)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 48 0 48 32 (SOff 25 0) _ HR0 Usp ltac:(gss_in));
  [ apply (den_atom0 E 25%nat _ E25'); lia | lia ]. }
assert (N40 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 40) 8 bg).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 48 0 48 40 (SOff 19 0) _ HR0 Usp ltac:(gss_in));
  [ apply (den_atom0 E 19%nat bg E19'); lia | lia ]. }
assert (N72 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 72) 8
              ((dxSA cx + 48) / 8 + SHADOW_OFF)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 72 88 72 88 72
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 48) (SLit 3)) (SOff 21 0)) _ HR2 Usp ltac:(gss_in));
  [ apply gss_den; apply (gss_U_shadow E 32 (dxSA cx) 48 E32 E21); unfold GS_PHI in *; lia
  | apply gss_shadow_range; unfold GS_PHI in *; lia ]. }
assert (N80 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 80) 8 (re_hp e1)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 72 88 72 88 80 (SOff 33 0) _ HR2 Usp ltac:(gss_in));
  [ apply (den_atom0 E 33%nat (re_hp e1) E33); unfold GS_PHI in *; lia | unfold GS_PHI in *; lia ]. }
assert (FR2 : dr_frame RG cx W1 (ms_mem ms0)).
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (G208 & G96 & G128 & G88 & G184 & G120 & G112 & G104 & G144 & G152 & G168 & G136 & G160 & G224 & G216 & G176 & Gsvd).
  repeat split;
    try (apply (gss_vm_keep W1 m1 (ms_mem ms0) _ 8%nat _);
         [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | assumption]).
  intros i Hi. apply (gss_vm_keep W1 m1 (ms_mem ms0) _ 8%nat _);
    [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact (Gsvd i Hi)]. }
pmkst HS.
eapply (LOOP cx s1 D p q 0%nat (length (re_keys e1))); [exact HB | | exact HDLN | exact HGA | exact HGF].
unfold GSL.
exists (ms_regs ms0), ly1, S1, (ms_mem ms0). eexists. eexists.
exists e1, h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl, kd, jj, bg.
split; [unfold cfg_at; reflexivity|].
split; [unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp|].
split; [rewrite (HK 3%bv ltac:(cbv; tauto)); exact R3|].
split; [rewrite (HK 4%bv ltac:(cbv; tauto)); exact R4|].
split; [rewrite (HK 18%bv ltac:(cbv; tauto)); exact R18|].
split; [rewrite (HK 9%bv ltac:(cbv; tauto)); exact R9|].
split; [rewrite (HK 8%bv ltac:(cbv; tauto)); exact R8|].
split; [rewrite (HK 21%bv ltac:(cbv; tauto)); exact R21|].
split; [exact FR2|].
split; [apply (gss_vm_keep W1 m1 (ms_mem ms0) _ 8%nat _);
  [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact M192]|].
split; [apply (gss_vm_keep W1 m1 (ms_mem ms0) _ 8%nat _);
  [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact M200]|].
split; [apply (gss_vm_keep W1 m1 (ms_mem ms0) _ 8%nat _);
  [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact M56]|].
split; [apply (gss_vm_keep W1 m1 (ms_mem ms0) _ 8%nat _);
  [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact M48]|].
split; [apply (gss_vm_keep W1 m1 (ms_mem ms0) _ 8%nat _);
  [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact M64]|].
split; [exact N8|]. split; [exact N16|]. split; [exact N24|]. split; [exact N32|].
split; [exact N40|]. split; [exact N72|]. split; [exact N80|].
split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23|].
split; [rewrite (HK 24%bv ltac:(cbv; tauto)); exact H24|].
split; [rewrite P19; apply gss_den;
  replace (Z.of_nat 0) with 0 by reflexivity; rewrite Z.mul_0_r, Z.add_0_r;
  apply (gss_U_shadow2 E 33 (re_hp e1) E33 E21); unfold GS_PHI in *; lia|].
split; [rewrite P20; apply gss_den; rewrite U_lit by lia; reflexivity|].
split; [rewrite P25; apply gss_den; apply (gss_U_sll3 E 34 (re_nheld e1) E34); lia|].
split; [rewrite P27; apply gss_den;
  rewrite (gss_U_sub E 24 25 (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat p + Z.of_nat jj)
    E24' E25' ltac:(lia) ltac:(lia) ltac:(lia)); lia|].
split; [unfold re_nheld in Hc; lia|].
split; [unfold re_nheld in Hc; lia|].
split; [intros i Hi; lia|].
split; [exact Hbgr|]. split; [exact Hbgk|]. split; [exact Hgest|]. split; [exact Hjjr|].
split; [unfold GSF; split; [exact Hbd|]; split; [exact Hpq|]; split; [exact Hq0|];
  split; [exact Hnz|]; split; [exact Hskp | exact Hlim]|].
split; [|exact HFUT].
apply (gss_core_kept cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl _ _ _
  ltac:(unfold DRAIN_FRAME, DRAIN_STK in *; lia) ltac:(lia) HJ4 ltac:(lia) ltac:(lia) HLC HJ
  ltac:(intros x Hx Hno; apply KEEP2; [exact Hx | unfold DRAIN_FRAME in *; lia | unfold DRAIN_FRAME in *; lia])
  PRES2).
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice D, 2026-10-30): the stage's set-up over W_drain_cx_x.v's Section
   variables (B PST ARx MT RP MMAX RG), the entry's ghost list Hp and budget kr after cx and the cut's own ghost list
   Hp1 after S1 (W_drain_gs.v's GSB_x / GA_x, W_gsscanb_cx.v's GSL_x).  Everything above this line is unchanged.
   - The stage calls no allocator rule: the cut's journal, its dbud_x and its trace pass unchanged from DGS_x to GA_x
     (nheld <= 0) and to GSL_x (the held-key loop's head at n = 0).
   - The AR-free names of Section c above (the byte lemmas gss_bz* / gss_garr8_* / gss_entry_*, the symbolic state
     gse_* and gse_entry, gss_img_low, gss_recs_len, gss_vm_keep, the U lemmas, GS_PHI, GSBx, GS_Bspan, GS_KEPT and
     GS_KEPT1) are CITED, with the RG / HGSB arguments their Section c proofs abstract.  The lemmas whose statement
     names AR, ajournal_gx or GSB have their _x twins
     (gss_blk_low_x .. gss_aout_fp_low_x, gss_core_kept_x); the tactics this part uses are restated with _x names.
   - The table block's shadow is read off the laws under HP0 (W_journal_x.v range_addressable_of_block_hp0_x). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_cx W_drain_cx_x W_drain_gs W_gsscanb_cx.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
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
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* ---- (3a) Lowness over ARx: the live blocks' bytes lie below the allocator ceiling (the law alx_blocks). ---- *)
Lemma gss_blk_low_x : forall ly S Hp (W : world SEGS) mem md qq nn a,
ARx ly S Hp W mem md -> In (qq, nn) (ablocks B ly S) -> qq <= a -> a < qq + req_size nn ->
0 <= a < alloc_ceiling.
Proof.
intros ly S Hp W mem md qq nn a HAR Hin H1 H2.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md qq nn HAR Hin) as (_ & H4096 & Hceil & _). lia.
Qed.

Lemma gss_aentry_fp_low_x : forall ly S Hp (W : world SEGS) mem md e,
ARx ly S Hp W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S Hp W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (HPK : forall k, In k (re_keys e) ->
  key_addr k <= a < key_addr k + Z.of_nat (length (bzs (key_text k ++ [Z_to_bv 8 0]))) ->
  0 <= a < alloc_ceiling).
{ intros k Hk Hak. rewrite gss_bzs_len, length_app in Hak. cbn [length] in Hak.
  rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
  apply (gss_blk_low_x ly S Hp W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR Hin); [lia|].
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia. }
assert (HPH : re_hp e <= a < re_hp e + Z.of_nat (length (bzs (key_ptrs (re_keys e)))) ->
  0 <= a < alloc_ceiling).
{ intros Hah. rewrite gss_bzs_len, gs_key_ptrs_len in Hah.
  destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
  - rewrite Hke in Hah. cbn [length] in Hah. lia.
  - apply (gss_blk_low_x ly S Hp W mem md (re_hp e) (re_kh e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq). unfold re_nheld in Hk1. lia. }
unfold aentry_fp in Hr.
destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [app In] in Hr.
- destruct Hr as [<- | Hr]; [unfold gfp in Ha; cbn [fst snd] in Ha; exact (HPH Ha)|].
  apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
- destruct Hr as [<- | [<- | Hr]].
  + unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gss_bzs_len, length_app in Ha.
    destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gss_blk_low_x ly S Hp W mem md (re_buf e) (re_cap e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia.
  + unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPH Ha).
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha. exact (HPK k Hk Ha).
Qed.

Lemma gss_alist_fp_low_x : forall ly S Hp (W : world SEGS) mem md LA l lines lo hi,
ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= 0x5fb000 ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S Hp W mem md LA l lines lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (gss_img_low RG HGSB a lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gss_bzs_len, length_app, (gss_recs_len RG) in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (gss_blk_low_x ly S Hp W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n, AREC in *. lia.
  + apply in_map_iff in Hr as (qq & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    rewrite gss_bzs_len, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs qq Hq) as (Hin & _).
    apply (gss_blk_low_x ly S Hp W mem md (fst qq) (Z.of_nat (length (snd qq)) + 1) a HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd qq)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma gss_asrc_fp_low_x : forall ly S Hp (W : world SEGS) mem md HA h,
ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S Hp W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (gss_img_low RG HGSB a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. rewrite gss_bzs_len in Ha.
  apply (gss_blk_low_x ly S Hp W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- unfold ASRC in *. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + eapply (gss_alist_fp_low_x ly S Hp W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * 96));
      [exact HAR | exact Hpend | lia | lia | lia | lia | exact Hr | exact Ha].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * eapply (gss_alist_fp_low_x ly S Hp W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hexp | lia | lia | lia | lia | exact Hr | exact Ha].
    * eapply (gss_alist_fp_low_x ly S Hp W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * 96));
        [exact HAR | exact Hheld | lia | lia | lia | lia | exact Hr | exact Ha].
Qed.

Ltac gss_ing_x := unfold G_DR, G_SL; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma gss_aout_fp_low_x : forall ly S Hp (W : world SEGS) mem md c O mx no cap out,
ARx ly S Hp W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S Hp W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof asan_consts as (C1 & _).
assert (GL2 : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> 0 <= a < alloc_ceiling).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (pa_img_range _ (proj1 (HG a HI))). lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (gss_img_low RG HGSB a (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL2 (rg_nout RG) 8); [gss_ing_x | lia].
- apply (GL2 (rg_capout RG) 8); [gss_ing_x | lia].
- apply (GL2 (rg_out RG) 8); [gss_ing_x | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (gss_img_low RG HGSB a (rg_client RG) (rg_client RG + 4)); lia.
- apply (GL2 (rg_client_broken RG) 1); [gss_ing_x | lia].
- pose proof (pa_obj_img 12 ltac:(lia)) as H12. rewrite HV12 in H12.
  apply (gss_img_low RG HGSB a (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL2 (rg_send_eintr RG) 1); [gss_ing_x | lia].
- apply (GL2 (as_errno B) 4); [gss_ing_x | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (gss_blk_low_x ly S Hp W mem md out cap a HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

(* ---- the tactics of the stage's runs (Section c's, restated) ---- *)
Ltac gss_rreg_x HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?Ev ?ssv (restrict ?H ?msv) =>
  pose proof (st_ok_pi_restrict_reg H Ev ssv msv r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ssv) r) in
  change (sr_get (ss_regs ssv) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

Ltac gss_in_x := cbn [In]; repeat first [left; reflexivity | right].

Ltac gss_nowr_x Usp :=
  let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (rr & Hin & Hr); cbn [ss_mem add_cond add_atom In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr;
      unfold DRAIN_FRAME in *; lia |]);
  destruct Hin.

Ltac gss_awr_x Usp :=
  apply awr_ok_x_of0; awr_ok_tac;
  repeat (eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- DRAIN_FRAME));
          [ reflexivity
          | rewrite Usp; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_wlo]; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_whi]; unfold DRAIN_FRAME; lia
          | awr_ok_tac ]).


(* The pieces of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cf rules and every carrier or statement it names
   -> their R twins; every other token is the strict text's. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* ---- (3b) The cut survives the stage, over GSB_x and the generic journal (the cut's Hp1 is kept). ---- *)
Lemma gss_core_kept_xR : forall cx Hp kr s1 D p q ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  m2 md2 k2,
alloc_ceiling + 88 <= dsp0 cx - DRAIN_FRAME -> dsp0 cx <= 2 ^ 47 -> (dxj cx < 4)%nat ->
4096 <= dxSA cx -> dxSA cx + 56 <= alloc_ceiling ->
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME <= x < dsp0 cx - DRAIN_FRAME + 88) ->
   aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m2 x) ->
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m2 md2 k2 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m2 md2 k2 HLOW HTOP HJ4 HSA1 HSA2 HGS HJ2
  KEEP PRES.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold GSB_xR, LCORE_xR in HGS |- *.
destruct HGS as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpres & Hframes & HFR & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (KL : forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x)
  by (intros x Hx; apply KEEP; lia).
assert (KF : forall x, dsp0 cx - DRAIN_FRAME + 88 <= x < dsp0 cx -> aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x)
  by (intros x Hx; apply KEEP; unfold DRAIN_FRAME in *; lia).
assert (AK : forall fp, (forall r, In r fp -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling) ->
  akept W1 m1 W1 m2 fp) by (intros fp Hlow; exact (gs_akept_of W1 m1 m2 fp KL PRES Hlow)).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (HBLK : forall b, In b (aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap
    (dvirt cx s1 false (dlH cx s1 p) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q))) out1) ->
  In b (ablocks B ly1 S1)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact Hperm | right].
  apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb|right].
  apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; exact Hb|right].
  apply in_or_app. left. exact Hb. }
split; [|split; [exact HLINK | split; [exact HSAME | split; [exact HHIST | split; [exact HRS | exact HBUD]]]]].
split; [exact HJ2|].
split.
{ intros x Hx. rewrite KL; [exact (Hrom x Hx)|].
  destruct Hx as (sg & Hsg & _ & Hr).
  pose proof (pa_img_range x ltac:(exists sg; split; [exact Hsg | exact Hr])). lia. }
split; [intros x Him Hno Her Hpx; exact (PRES x (Hpres x Him Hno Her Hpx))|].
split; [exact Hframes|].
split.
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224 & F216 & F176 & Hsvd).
  repeat split;
    try (apply (gss_vm_keep RG W1 m1 m2 _ 8%nat _);
         [intros x Hx; apply KF; unfold DRAIN_FRAME in *; lia | assumption]).
  intros i Hi. apply (gss_vm_keep RG W1 m1 m2 _ 8%nat _);
    [intros x Hx; apply KF; unfold DRAIN_FRAME in *; lia | exact (Hsvd i Hi)]. }
(* the relay entry's 56 bytes lie in the table block *)
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR1 HTB) as (_ & HG4096 & HGceil & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.

split.
{ apply (gss_garr8_kept W1 m1 W1 m2); [exact Hgarr|].
  intros x Hx. rewrite gss_bzs_len in Hx. apply KL.
  assert (HL56 : length (entry_bytes e1) = 56%nat).
  { pose proof HOKX as (_ & _ & Hp1' & Hp2' & _). unfold entry_bytes.
    rewrite !length_app, Hp1', Hp2', !Mem.length_le8, !Mem.length_le4. reflexivity. }
  rewrite HL56 in Hx. unfold ATABLE, AENT in *. lia. }
split.
{ intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hawr i Hi). }
split.
{ eapply (gs_aentry_okx_kept B RG).
  - exact HOKX.
  - apply AK. exact (gss_aentry_fp_low_x ly1 S1 Hp1 W1 m1 md1 e1 HAR1 HOKX).
  - intros b Hb. apply HBLK. apply in_or_app. left. exact Hb. }
split.
{ eapply asrc_at_kept.
  - exact Hsrc.
  - apply AK. apply (gss_asrc_fp_low_x ly1 S1 Hp1 W1 m1 md1 (dHA RG cx) h1 HAR1 Hsrc);
      unfold dHA, ASRC in *; lia.
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. left. exact Hb. }
split.
{ pose proof HGSB as (Hg1 & Hg2 & _). unfold aothers_at in Hoth |- *.
  intros i Hi Hij. destruct (Hoth i Hi Hij) as (f & o & Mf & Mo & Hfo).
  exists f, o. split; [|split; [|exact Hfo]];
  apply (gss_vm_keep RG W1 m1 m2 _ 4%nat _); [| exact Mf | | exact Mo];
  intros x Hx; apply KL; apply (gss_img_low RG HGSB x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia. }
split.
{ intros x Hx Hnx. destruct (Hgsk x Hx Hnx) as (Hv & Hw). split.
  - rewrite KL; [exact Hv|]. pose proof HGSB as (Hg1 & Hg2 & _).
    apply (gss_img_low RG HGSB x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
  - intros Hwr. unfold arm. apply (writable_kept (w_H W1) m1 m2 _ (PRES _)). exact (Hw Hwr). }
split.
{ eapply aout_at_kept.
  - exact Hout.
  - apply AK. exact (gss_aout_fp_low_x ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ HAR1 Hout).
  - intros b Hb. apply HBLK. apply in_or_app. right. apply in_or_app. right. exact Hb. }
split; [exact Hlivout | exact Hperm].
Qed.
(* The stage over ARx, given the held-search loop over ARx (lib/A/W_gsscanb_cx.v gs_scan_loop_stmt_x). *)
Theorem gs_scan_of_loop_xR : gs_scan_loop_stmt_xR B PST ARx MT RP MMAX RG R -> gs_scan_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros LOOP.
unfold gs_scan_stmt_xR. intros cx Hp kr s1 D p q W1 c1 HB HGS HDLN HGA HGF.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 336) by reflexivity.
assert (HDS : DRAIN_STK_x = 16976) by reflexivity.
unfold DGS_xR in HGS.
destruct HGS as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks
  & tl & kd & jj & bg & Hcfg & Hregs & H23 & H24 & H25 & H19 & Hbgr & Hbgk & Hgest & Hjjr
  & Hbd & Hpq & Hq0 & Hnz & Hskp & Hlim & HLC & HFUT).
pose proof Hregs as (Hsp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64).
pose proof HFR as (F208 & F96 & F128 & F88 & F184 & F120 & F112 & F104 & F144 & F152 & F168 & F136 & F160 & F224 & F216 & F176 & Hsaved).
pose proof HLC as HLC'. unfold LCORE_xR in HLC'.
destruct HLC' as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpresk & Hframes & _ & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & HBx10 & Htbl & HSAlo & HSAhi & Hgarr0 & Hawr0 & Hent0 & HJ4 & HBrest).
pose proof Hafn as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
fold (dsp0 cx) in Hal16, Hslo, Hshi, Htop1.
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (HG16 & HG4096 & HGceil & HGia & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
unfold ATABLE, AENT in *.
pose proof HOKX as (Heof & Hskipe & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & HND1 & HND2 & Hkeys).
(* the journal's stack: the frame is present, hence writable *)
pose proof HJ as (HSTKj & HXOj & (memS & HJi & HAGj) & HOUTj).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRESj & _).
assert (WRF : forall x, dsp0 cx - DRAIN_STK_x <= x < dsp0 cx -> writable_at SEGS (arm W1 m1) x)
  by (intros x Hx; apply (apresent_writable SEGS); apply HPRESj; lia).
(* the two cells the search reads off the relay entry *)
assert (HHPR : 0 <= re_hp e1 <= GS_PHI).
{ destruct Hheld as [(Hz & _)|(Hz & Hin & Hk1 & Hk2 & _)]; [unfold GS_PHI; lia|].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (_ & H4 & Hc & _).
  pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (Hr1 & Hr2). unfold GS_PHI. lia. }
assert (HNHR : 0 <= re_nheld e1 < 2 ^ 26) by (split; [unfold re_nheld; lia | exact Hnheld]).
pose proof (gss_entry_hp RG HGSB W1 m1 (dxSA cx) e1 Hpad1 ltac:(unfold GS_PHI in HHPR; lia) Hgarr) as MHP.
pose proof (gss_entry_nheld RG HGSB W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MNH.
(* the symbolic state at 0x837c8 *)
pose proof (gse_entry RG W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_hp e1) (re_nheld e1)
  Hsp ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity) R21
  ltac:(lia) ltac:(unfold GS_PHI; lia) ltac:(lia) HHPR HNHR
  ltac:(intros o Ho; apply WRF; lia) ltac:(intros o Ho; apply WRF; lia)
  M48 M56 F96 F128 MHP MNH) as HS.
remember (Eimg (Ereg regs1 (gse_extra (dxSA cx) (re_hp e1) (re_nheld e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (gse_extra (dxSA cx) (re_hp e1) (re_nheld e1))) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EREG 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_hp e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_nheld e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (HBx : U E GSBx = SHADOW_OFF)
  by (unfold GSBx; rewrite (U_atom E 21 SHADOW_OFF E21) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS GSBx gse_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E GSBx 32 (dxG cx) 896 (dxSA cx) 40 56).
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (dxG cx) 896);
      [exact HAR | exact HTB | lia | rewrite RQT; lia].
  - exact HBx.
  - apply (U_atom E 32 (dxSA cx) E32). unfold GS_PHI in *. lia.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. rewrite RQT in HGia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_seen)) with (Z_to_bv 64 (BASE + A_dr_seen)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
paj_run_tok_xR RUNR HS HJ SHOK GS_Bspan. { gss_awr_x Usp. }
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ => rename Hg into GR1 end.
(* the run to the nheld test wrote only 72(sp) *)
assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME <= x < dsp0 cx - DRAIN_FRAME + 48) ->
  ~ (dsp0 cx - DRAIN_FRAME + 72 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
  aview SEGS (w_H W1) (ms_mem ms) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno Hno'. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr x Hx).
  intros (r & Hin & Hr). cbn [ss_mem ss_gse gse_regions In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi gse_frameW gse_frameR gse_frameW2 gse_frameR2 gse_ent base_val] in Hr;
  rewrite ?Usp in Hr; unfold DRAIN_FRAME in *; lia. }
assert (PRES1 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms) x)
  by (intros x Hpx; exact (apresent_grows _ _ _ _ GR1 Hpx)).
clear HF HFr GR1.
psrr_branch_tok RUNR BRR HS SHOK GS_Bspan.
-
(* nheld <= 0: nothing is held, so the key is not held; n = 0 at 0x83898, on to GA_x. *)
unfold branch_taken in Hc. cbn [sv_denot] in Hc.
rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
rewrite (gss_lts_lit RG 0 (re_nheld e1) ltac:(lia) ltac:(lia)) in Hc.
apply Bool.negb_true_iff, Z.ltb_ge in Hc.
assert (HN0 : re_nheld e1 = 0) by lia.
assert (HKE : re_keys e1 = []) by (apply length_zero_iff_nil; unfold re_nheld in HN0; lia).
paj_run_to_tok_xR RUNTOR HS HJ SHOK GS_Bspan A_dr_add. { gss_awr_x Usp. }
match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem ms0)) |- _ =>
  rename Hg into GR2 end.
assert (KEEP2 : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME <= x < dsp0 cx - DRAIN_FRAME + 48) ->
  ~ (dsp0 cx - DRAIN_FRAME + 72 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
  aview SEGS (w_H W1) (ms_mem ms0) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno Hno'. rewrite <- (KEEP1 x Hx Hno Hno').
  apply (aview_kept_out E _ (w_H W1) (ms_mem ms) (ms_mem ms0) HFr x Hx). gss_nowr_x Usp. }
assert (PRES2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms0) x)
  by (intros x Hpx; exact (apresent_grows _ _ _ _ GR2 (PRES1 x Hpx))).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ GS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (27%bv : bv 5) Q27.
(* the shadow slot the stage wrote at 72(sp) *)
assert (M72 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 72) 8
               ((dxSA cx + 48) / 8 + SHADOW_OFF)).
{ lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
    pose proof (st_ok_pi_region_nth Ev ssv msv 2 _ HS eq_refl) as HR72 end.
  cbn [ms_mem restrict] in HR72.
  apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 72 88 72 88 72
           (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 48) (SLit 3)) (SOff 21 0)) _ HR72 Usp
           ltac:(cbn [In]; left; reflexivity));
  [ apply gss_den; apply (gss_U_shadow RG E 32 (dxSA cx) 48 E32 E21); unfold GS_PHI in *; lia
  | pose proof (Z.div_pos (dxSA cx + 48) 8 ltac:(lia) ltac:(lia));
    pose proof (Z.div_lt_upper_bound (dxSA cx + 48) 8 (2 ^ 61) ltac:(lia) ltac:(unfold GS_PHI in *; lia));
    unfold SHADOW_OFF; lia ]. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ GS_KEPT1 HS HAE ltac:(vm_compute; reflexivity)) as HK1.
cbn [ms_regs restrict] in HK1.
assert (FR2 : dr_frame RG cx W1 (ms_mem ms0)).
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (G208 & G96 & G128 & G88 & G184 & G120 & G112 & G104 & G144 & G152 & G168 & G136 & G160 & G224 & G216 & G176 & Gsvd).
  repeat split;
    try (apply (gss_vm_keep RG W1 m1 (ms_mem ms0) _ 8%nat _);
         [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | assumption]).
  intros i Hi. apply (gss_vm_keep RG W1 m1 (ms_mem ms0) _ 8%nat _);
    [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact (Gsvd i Hi)]. }
assert (HdlH : dlH cx s1 p = []).
{ destruct HLINK as (_ & _ & _ & HKT & _). unfold dvirt in HKT. cbn [drain_b_c.ds_H] in HKT.
  rewrite <- HKT, HKE. reflexivity. }
pmkst HS.
apply HGA. unfold GA_xR.
exists (ms_regs ms0), ly1, S1, Hp1, (ms_mem ms0). eexists. eexists.
exists e1, h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl, kd, jj, bg.
split; [unfold cfg_at; reflexivity|].
split.
{ unfold dregs_line.
  split; [unfold spZ; rewrite (HK1 2%bv ltac:(cbv; tauto)); exact Hsp|].
  split; [rewrite (HK1 3%bv ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (HK1 4%bv ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (HK1 22%bv ltac:(cbv; tauto)); exact R22|].
  split; [rewrite (HK1 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [rewrite (HK1 18%bv ltac:(cbv; tauto)); exact R18|].
  split; [rewrite (HK1 9%bv ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (HK1 8%bv ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (HK1 21%bv ltac:(cbv; tauto)); exact R21|].
  split; [exact FR2|].
  repeat split; apply (gss_vm_keep RG W1 m1 (ms_mem ms0) _ 8%nat _);
    first [ intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | assumption ]. }
split; [rewrite (HK1 23%bv ltac:(cbv; tauto)); exact H23|].
split; [rewrite (HK1 24%bv ltac:(cbv; tauto)); exact H24|].
split; [rewrite (HK1 25%bv ltac:(cbv; tauto)); exact H25|].
split; [rewrite (HK1 19%bv ltac:(cbv; tauto)); exact H19|].
split; [rewrite Q10, HN0; reflexivity|].
split; [rewrite Q11, E34; reflexivity|].
split; [rewrite Q12, E32, (unsigned_lit_small (dxSA cx)) by (unfold GS_PHI in *; lia);
  rewrite (gss_srl3_lit RG) by (unfold GS_PHI in *; lia); reflexivity|].
split; [exact M72|].
split; [exact Hbgr|]. split; [exact Hbgk|]. split; [exact Hgest|]. split; [exact Hjjr|].
split; [rewrite HdlH; reflexivity|].
split; [unfold GSF; split; [exact Hbd|]; split; [exact Hpq|]; split; [exact Hq0|];
  split; [exact Hnz|]; split; [exact Hskp | exact Hlim]|].
split; [|exact HFUT].
apply (gss_core_kept_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl _ _ _
  ltac:(unfold DRAIN_FRAME, DRAIN_STK_x, DRAIN_STK in *; lia) ltac:(lia) HJ4 ltac:(lia) ltac:(lia) HLC HJ
  ltac:(intros x Hx Hno; apply KEEP2; [exact Hx | unfold DRAIN_FRAME in *; lia | unfold DRAIN_FRAME in *; lia])
  PRES2).
-
(* nheld > 0: the shadow check of &s->held, the spills, and the loop's registers, to 0x83838 with n = 0. *)
unfold branch_taken in Hc. cbn [sv_denot] in Hc.
rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
rewrite (gss_lts_lit RG 0 (re_nheld e1) ltac:(lia) ltac:(lia)) in Hc.
apply Bool.negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_tok_xR RUNTOR HS HJ SHOK GS_Bspan A_dr_hloop. { gss_awr_x Usp. }
gss_rreg_x HS (19%bv : bv 5) P19. gss_rreg_x HS (20%bv : bv 5) P20.
gss_rreg_x HS (25%bv : bv 5) P25. gss_rreg_x HS (27%bv : bv 5) P27.
match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem ms)) (mrestrict (w_H W1) (ms_mem ms0)) |- _ =>
  rename Hg into GR2 end.
assert (KEEP2 : forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME <= x < dsp0 cx - DRAIN_FRAME + 48) ->
  ~ (dsp0 cx - DRAIN_FRAME + 72 <= x < dsp0 cx - DRAIN_FRAME + 88) ->
  aview SEGS (w_H W1) (ms_mem ms0) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno Hno'. rewrite <- (KEEP1 x Hx Hno Hno').
  apply (aview_kept_out E _ (w_H W1) (ms_mem ms) (ms_mem ms0) HFr x Hx). gss_nowr_x Usp. }
assert (PRES2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem ms0) x)
  by (intros x Hpx; exact (apresent_grows _ _ _ _ GR2 (PRES1 x Hpx))).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ GS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
(* the line lies in the relay's buffer, so every address the loop's registers hold is small *)
assert (HUW : bzs (re_U e1) = dW s1)
  by (destruct HLINK as (_ & HU & _); unfold dvirt in HU; cbn [drain_b_c.ds_u] in HU; exact HU).
assert (HWlen : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HUW, gss_bzs_len; exact HUlen).
assert (HBUF : In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\ 0 < re_cap e1).
{ destruct Hbufc as [(Hc0 & Hb0 & Hu0)|(Hcpos & Hbin & Hjunk & Hbuf8)]; [exfalso; lia | split; assumption]. }
destruct HBUF as (HBin & HBcap).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR HBin)
  as (_ & HB4096 & HBceil & _).
assert (RQB : req_size (re_cap e1) = re_cap e1)
  by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQB in HBceil.
assert (HLINE : 0 <= re_buf e1 + Z.of_nat p /\ re_buf e1 + Z.of_nat p + Z.of_nat jj < 2 ^ 63).
{ split; [lia|]. assert (Z.of_nat q < re_used e1) by lia. lia. }
destruct HLINE as (HL1 & HL2).
assert (E24' : ew E 24 = Z_to_bv 64 (re_buf e1 + Z.of_nat p))
  by (rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl); exact H24).
assert (E25' : ew E 25 = Z_to_bv 64 (re_buf e1 + Z.of_nat p + Z.of_nat jj))
  by (rewrite (EREG 25%nat 25%bv ltac:(lia) eq_refl); exact H25).
assert (E19' : ew E 19 = Z_to_bv 64 bg) by (rewrite (EREG 19%nat 19%bv ltac:(lia) eq_refl); exact H19).
(* the seven frame slots the setup wrote *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_region_nth Ev ssv msv 0 _ HS eq_refl) as HR0;
  pose proof (st_ok_pi_region_nth Ev ssv msv 2 _ HS eq_refl) as HR2 end.
cbn [ms_mem restrict] in HR0, HR2.
assert (N8 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 8) 8
             ((dxSA cx + 40) / 8 + SHADOW_OFF)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 48 0 48 8
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 40) (SLit 3)) (SOff 21 0)) _ HR0 Usp ltac:(gss_in_x));
  [ apply gss_den; apply (gss_U_shadow RG E 32 (dxSA cx) 40 E32 E21); unfold GS_PHI in *; lia
  | apply (gss_shadow_range RG); unfold GS_PHI in *; lia ]. }
assert (N16 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 40) / 8)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 48 0 48 16
    (SAlu ALU_SRL (SOff 32 40) (SLit 3)) _ HR0 Usp ltac:(gss_in_x));
  [ apply gss_den; apply (gss_U_srl RG E 32 (dxSA cx) 40 E32); unfold GS_PHI in *; lia
  | pose proof (Z.div_pos (dxSA cx + 40) 8 ltac:(lia) ltac:(lia));
    pose proof (Z.div_lt_upper_bound (dxSA cx + 40) 8 (2 ^ 60) ltac:(lia) ltac:(unfold GS_PHI in *; lia));
    lia ]. }
assert (N24 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 24) 8 (re_nheld e1)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 48 0 48 24 (SOff 34 0) _ HR0 Usp ltac:(gss_in_x));
  [ apply (den_atom0 E 34%nat (re_nheld e1) E34); lia | lia ]. }
assert (N32 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 32) 8
              (re_buf e1 + Z.of_nat p + Z.of_nat jj)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 48 0 48 32 (SOff 25 0) _ HR0 Usp ltac:(gss_in_x));
  [ apply (den_atom0 E 25%nat _ E25'); lia | lia ]. }
assert (N40 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 40) 8 bg).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 48 0 48 40 (SOff 19 0) _ HR0 Usp ltac:(gss_in_x));
  [ apply (den_atom0 E 19%nat bg E19'); lia | lia ]. }
assert (N72 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 72) 8
              ((dxSA cx + 48) / 8 + SHADOW_OFF)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 72 88 72 88 72
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 48) (SLit 3)) (SOff 21 0)) _ HR2 Usp ltac:(gss_in_x));
  [ apply gss_den; apply (gss_U_shadow RG E 32 (dxSA cx) 48 E32 E21); unfold GS_PHI in *; lia
  | apply (gss_shadow_range RG); unfold GS_PHI in *; lia ]. }
assert (N80 : val_mem SEGS (arm W1 (ms_mem ms0)) (dsp0 cx - DRAIN_FRAME + 80) 8 (re_hp e1)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 72 88 72 88 80 (SOff 33 0) _ HR2 Usp ltac:(gss_in_x));
  [ apply (den_atom0 E 33%nat (re_hp e1) E33); unfold GS_PHI in *; lia | unfold GS_PHI in *; lia ]. }
assert (FR2 : dr_frame RG cx W1 (ms_mem ms0)).
{ unfold dr_frame in HFR |- *. cbv zeta in HFR |- *.
  destruct HFR as (G208 & G96 & G128 & G88 & G184 & G120 & G112 & G104 & G144 & G152 & G168 & G136 & G160 & G224 & G216 & G176 & Gsvd).
  repeat split;
    try (apply (gss_vm_keep RG W1 m1 (ms_mem ms0) _ 8%nat _);
         [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | assumption]).
  intros i Hi. apply (gss_vm_keep RG W1 m1 (ms_mem ms0) _ 8%nat _);
    [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact (Gsvd i Hi)]. }
pmkst HS.
eapply (LOOP cx Hp kr s1 D p q 0%nat (length (re_keys e1))); [exact HB | | exact HDLN | exact HGA | exact HGF].
unfold GSL_xR.
exists (ms_regs ms0), ly1, S1, Hp1, (ms_mem ms0). eexists. eexists.
exists e1, h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl, kd, jj, bg.
split; [unfold cfg_at; reflexivity|].
split; [unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp|].
split; [rewrite (HK 3%bv ltac:(cbv; tauto)); exact R3|].
split; [rewrite (HK 4%bv ltac:(cbv; tauto)); exact R4|].
split; [rewrite (HK 18%bv ltac:(cbv; tauto)); exact R18|].
split; [rewrite (HK 9%bv ltac:(cbv; tauto)); exact R9|].
split; [rewrite (HK 8%bv ltac:(cbv; tauto)); exact R8|].
split; [rewrite (HK 21%bv ltac:(cbv; tauto)); exact R21|].
split; [exact FR2|].
split; [apply (gss_vm_keep RG W1 m1 (ms_mem ms0) _ 8%nat _);
  [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact M192]|].
split; [apply (gss_vm_keep RG W1 m1 (ms_mem ms0) _ 8%nat _);
  [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact M200]|].
split; [apply (gss_vm_keep RG W1 m1 (ms_mem ms0) _ 8%nat _);
  [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact M56]|].
split; [apply (gss_vm_keep RG W1 m1 (ms_mem ms0) _ 8%nat _);
  [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact M48]|].
split; [apply (gss_vm_keep RG W1 m1 (ms_mem ms0) _ 8%nat _);
  [intros x Hx; apply KEEP2; unfold DRAIN_FRAME in *; lia | exact M64]|].
split; [exact N8|]. split; [exact N16|]. split; [exact N24|]. split; [exact N32|].
split; [exact N40|]. split; [exact N72|]. split; [exact N80|].
split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23|].
split; [rewrite (HK 24%bv ltac:(cbv; tauto)); exact H24|].
split; [rewrite P19; apply gss_den;
  replace (Z.of_nat 0) with 0 by reflexivity; rewrite Z.mul_0_r, Z.add_0_r;
  apply (gss_U_shadow2 RG E 33 (re_hp e1) E33 E21); unfold GS_PHI in *; lia|].
split; [rewrite P20; apply gss_den; rewrite U_lit by lia; reflexivity|].
split; [rewrite P25; apply gss_den; apply (gss_U_sll3 RG HGSB E 34 (re_nheld e1) E34); lia|].
split; [rewrite P27; apply gss_den;
  rewrite (gss_U_sub RG HGSB E 24 25 (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat p + Z.of_nat jj)
    E24' E25' ltac:(lia) ltac:(lia) ltac:(lia)); lia|].
split; [unfold re_nheld in Hc; lia|].
split; [unfold re_nheld in Hc; lia|].
split; [intros i Hi; lia|].
split; [exact Hbgr|]. split; [exact Hbgk|]. split; [exact Hgest|]. split; [exact Hjjr|].
split; [unfold GSF; split; [exact Hbd|]; split; [exact Hpq|]; split; [exact Hq0|];
  split; [exact Hnz|]; split; [exact Hskp | exact Hlim]|].
split; [|exact HFUT].
apply (gss_core_kept_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl _ _ _
  ltac:(unfold DRAIN_FRAME, DRAIN_STK_x, DRAIN_STK in *; lia) ltac:(lia) HJ4 ltac:(lia) ltac:(lia) HLC HJ
  ltac:(intros x Hx Hno; apply KEEP2; [exact Hx | unfold DRAIN_FRAME in *; lia | unfold DRAIN_FRAME in *; lia])
  PRES2).
Qed.
End wR.


(* ---- (3b) The cut survives the stage, over GSB_x and the generic journal (the cut's Hp1 is kept). ---- *)
Lemma gss_core_kept_x : forall cx Hp kr s1 D p q ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  m2 md2 k2,
alloc_ceiling + 88 <= dsp0 cx - DRAIN_FRAME -> dsp0 cx <= 2 ^ 47 -> (dxj cx < 4)%nat ->
4096 <= dxSA cx -> dxSA cx + 56 <= alloc_ceiling ->
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k2 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (dsp0 cx - DRAIN_FRAME <= x < dsp0 cx - DRAIN_FRAME + 88) ->
   aview SEGS (w_H W1) m2 x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m2 x) ->
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m2 md2 k2 e1 h1 out1 ev1 LB1 spent tl.
Proof. eapply (gss_core_kept_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* The stage over ARx, given the held-search loop over ARx (lib/A/W_gsscanb_cx.v gs_scan_loop_stmt_x). *)
Theorem gs_scan_of_loop_x : gs_scan_loop_stmt_x B PST ARx MT RP MMAX RG -> gs_scan_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (gs_scan_of_loop_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.
End cx.
End bx.
End ax.
