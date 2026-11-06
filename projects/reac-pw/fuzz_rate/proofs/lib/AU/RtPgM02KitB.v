(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyBase.v, RPgM02KeyI.v and RPgM02KeyV.v
   at 595d8c5dd1b5 (the value language of the value entry's address and of a `lw`, the expect_value cases, the
   shadow entry over the value entry, the value dispatch, the Int arm and the value tail),
   proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyF.v at 7e8cf15c304a (the Float arm: the size test, the `flw` and
   pod_nearest) and proofs/reac-pw/fuzz_rate/lib/A/RtPgScanF.v at 22306b8175e6 (the pairs of the scan across a
   key) for reac-pw/fuzz_rate image A: role's pcs become rate's, the shadow base is rate's s2 (atom 18), role's Role
   answers become Rate.expect_value / Rate.rate_of_pairs, role's value tail (a bound test and check_role) becomes
   rate's check_rate on the hz cell, the out cell is R+0x158, the `flw` is stepped by YA0n.SRr_step, and the key
   compare (the spills, the strcmp wrapper, the mismatch exit to O) is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02Tail.v at 1d255703e887 (its two check
   walks ch_mal / ch_abs and the cut lemma ch_cut_T, with the call-in-the-middle pattern they take from
   lib/A/RPgCheckStr.v) for reac-pw/fuzz_rate image A: role's pcs become rate's (ABS 0x82b7c, MAL 0x82c9c, the
   join A 0x82ca8), the one-byte role cell becomes rate's four-byte hz cell holding 0x5a5a5a5a, the register the
   cell's address lives in moves from role's s6 to rate's s5 (atom 21), the two real-frame cells the absent arm
   reloads are rate's R+0x78 (F) and R+0x58 (the flags byte) instead of role's R+0x28 and R+0x80, and the join's
   cut is rs_cut_A, which carries the flags byte where role's rs_cut_T carried the first block. *)
(* Modified by Theorem Labs, 2026-10: the shared parts of proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Key.v at
   48d3cf0d8e40 (the model facts, the value language of a `lw`, the value entry's facts, the interfaces of the
   pieces and their chain, the transport of a cut across the half's runs and calls) and of
   proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Chk.v at 5e00caea0758 (ch_L, ch_K, ch_far, ch_garr8_kept, ch_cut_A) for
   image B (fuzz_rate.asan-ubsan): the cuts are lib/AU/RtPgSegB.v's (rs_ -> rsb_); rsb_L_chk's registers are s0, s1,
   s3, s4, s5 and its cells R+0x178, R+0x10, R+0x50 and the six header cells; the join's cut carries s10 = the
   answer's code, s6 = the mask and s7 = the flags byte (image A: s8, s6 = F, s10 = the flags byte); the hz cell is
   at F+0x2a0; the zone the half writes is image B's four spill cells R+0x140, R+0x150, R+0x158, R+0x160 and
   pod_nearest's out cell R+0x198; the shadow base is s4 (atom 20); the value entry's interfaces carry the registers
   image B's readers use (a7 = &ent[0] + 4, s8 = 104 v, a4 = pp) and the cells R+0x170 (the code) and R+0x138
   (0x4018). The mulhu form of &ent[v] is image A's only and is dropped. *)
(* reac-pw/fuzz_rate, image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded code bytes are the pin's): the
   shared layer of the walk files of M02's match half (lib/AU/RtPgM02BaseB.v lists the code). Statement text and
   shared lemmas only. Proves no function (kind: statement text).

   THE PIECES (each one stretch of code; the files that prove them):
     KM  0x82c40 -> O (mismatch, at = m + 2) / KV       m2kb_key_stmt     lib/AU/RtPgM02KeyCB.v
     KV  0x82c98 -> FLT / MAL / JN (type, Int arm)      m2kb_val_stmt     lib/AU/RtPgM02KeyVB.v
     FLT 0x82d70 -> MAL / JN (size, flw, pod_nearest)   m2kb_float_stmt   lib/AU/RtPgM02KeyFB.v
     JN  0x82dd0 -> A (check_rate)                      m2kb_join_stmt    lib/AU/RtPgM02KeyVB.v
     ABS 0x82d1c / MAL 0x82de0 -> A                     rsb_piece_W11b_checks_stmt   lib/AU/RtPgM02ChkB.v
   m2kb_chain chains the first four into rsb_piece_W11b_key_stmt. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Nearest Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB RtPgMemB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCheck RtPgM02BaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ===================================== the pcs the pieces meet at ===================================== *)
Definition M2KB_FLT : Z := 0x82d70.     (* the Float arm: add a1,a7,s8 *)
Definition M2KB_JN : Z := 0x82dd0.      (* the two arms meet: lw a1,0(s5) *)

(* ===================================== the value language of a `lw` ===================================== *)
(* m2kb_sx and its lemmas: the 64-bit word an `lw` leaves for a 32-bit pattern [A's m2k_sx]. *)
Definition m2kb_sx (v : Z) : Z := if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32).

Lemma m2kb_U_sext32 : forall E (n : nat) (v : Z),
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt true 32 (SOff n 0)) = m2kb_sx v.
Proof.
intros E n v H Hv.
rewrite U_SExt, (U_atom E n v H ltac:(lia)).
cbn [Z.of_N].
rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold m2kb_sx, zcanon, M64, bv_swrap, bv_wrap.
change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
destruct (Z.ltb_spec v (2 ^ 31)) as [Hl|Hl]; cbv beta iota.
- rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia.
  rewrite Z.mod_small by lia. lia.
- replace ((v + 2 ^ 31) mod 2 ^ 32) with (v + 2 ^ 31 - 2 ^ 32)
    by (apply (Z.mod_unique _ _ 1); lia).
  symmetry. apply (Z.mod_unique _ _ (-1)); lia.
Qed.

Lemma m2kb_sx_eq : forall v w, 0 <= v < 2 ^ 32 -> 0 <= w < 2 ^ 31 -> (m2kb_sx v = w <-> v = w).
Proof.
intros v w Hv Hw. unfold m2kb_sx.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; split; intros; lia.
Qed.

Lemma m2kb_sx_range : forall v, 0 <= v < 2 ^ 32 -> 0 <= m2kb_sx v < 2 ^ 64.
Proof.
intros v Hv. unfold m2kb_sx.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; lia.
Qed.

Lemma m2kb_sx_id : forall v, 0 <= v < 2 ^ 31 -> m2kb_sx v = v.
Proof.
intros v Hv. unfold m2kb_sx.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; lia.
Qed.

Lemma m2kb_denot_of_U : forall E (a : sv) (v : Z), U E a = v -> sv_denot E a = Z_to_bv 64 v.
Proof.
intros E a v H. rewrite (denot_lit_U E a), H. reflexivity.
Qed.

(* the int32 value of a 32-bit pattern has the pattern as its low 32 bits *)
Lemma m2kb_s32_mod : forall z, 0 <= z < 2 ^ 32 -> Accessors.s32 z mod 2 ^ 32 = z.
Proof.
intros z Hz. unfold Accessors.s32.
destruct (Z.ltb_spec z (2 ^ 31)); cbv beta iota.
- apply Z.mod_small. lia.
- symmetry. apply (Z.mod_unique _ _ (-1)); lia.
Qed.

(* a register's value as the denotation of its symbolic value, without unfolding sv_denot *)
Ltac m2kb_rsv HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Hr : getr (ms_regs ms) r = sv_denot E e)
by (refine (eq_trans (st_ok_restrict_reg segs H E ss ms r HS) (f_equal (sv_denot E) _)); vm_compute; reflexivity)
end.

(* ===================================== the model facts ===================================== *)
(* What a key entry is, the text of a NUL-terminated body, the pairs of the scan across the key, what the value
   entry's type and size decide, and the record's bounds (lib/Pod's Rate / Accessors / Layout). [A's m2k_ lemmas] *)
Definition m2kb_d : ent := Ent 0 0 [].

Lemma m2kb_skipn_cons : forall {A : Type} (l : list A) (j : nat) (d : A), (j < length l)%nat ->
skipn j l = nth j l d :: skipn (S j) l.
Proof.
intros A l. induction l as [|x l IH]; intros j d Hj; cbn [length] in Hj; [lia|].
destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in Hj. lia.
Qed.

Lemma m2kb_pairs_skip : forall (es : list ent) (m : nat), (m < length es)%nat ->
key_of (nth m es m2kb_d) = None ->
pairs_by key_of (skipn m es) None = pairs_by key_of (skipn (S m) es) None.
Proof.
intros es m Hm Hk. rewrite (m2kb_skipn_cons es m m2kb_d Hm). cbn [pairs_by]. rewrite Hk. reflexivity.
Qed.

Lemma m2kb_pairs_run : forall (es : list ent) (a m : nat), (a <= m)%nat -> (m <= length es)%nat ->
(forall q, (a <= q < m)%nat -> key_of (nth q es m2kb_d) = None) ->
pairs_by key_of (skipn a es) None = pairs_by key_of (skipn m es) None.
Proof.
intros es a m. remember (m - a)%nat as n eqn:Hn. revert a m Hn.
induction n as [|n IH]; intros a m Hn Ham Hml Hq.
- assert (a = m) as -> by lia. reflexivity.
- rewrite (m2kb_pairs_skip es a ltac:(lia) (Hq a ltac:(lia))).
  apply (IH (S a) m); [lia | lia | lia |]. intros q Hqq. apply Hq. lia.
Qed.

Lemma m2kb_pairs_key : forall (es : list ent) (m : nat) (kb : list byte), (S m < length es)%nat ->
key_of (nth m es m2kb_d) = Some kb ->
pairs_by key_of (skipn m es) None = (kb, nth (S m) es m2kb_d) :: pairs_by key_of (skipn (S (S m)) es) None.
Proof.
intros es m kb Hm Hk.
rewrite (m2kb_skipn_cons es m m2kb_d ltac:(lia)). cbn [pairs_by]. rewrite Hk.
rewrite (m2kb_skipn_cons es (S m) m2kb_d Hm). cbn [pairs_by]. reflexivity.
Qed.

(* the scan's invariant at the key m: the pairs are (kb, ent[m + 1]), then the pairs from m + 2 on *)
Lemma m2kb_inv_key : forall (rec : pod_rec) (a m : nat) (kb : list byte), rsb_scan_inv rec a ->
(a <= m)%nat -> (S m < length (ents rec))%nat ->
(forall q, (a <= q < m)%nat -> key_of (nth q (ents rec) m2kb_d) = None) ->
key_of (nth m (ents rec) m2kb_d) = Some kb ->
rsb_E0 rec = Rate.rate_of_pairs Rate.expect_value
 ((kb, nth (S m) (ents rec) m2kb_d) :: pairs_by key_of (skipn (S (S m)) (ents rec)) None).
Proof.
intros rec a m kb (Hle & He) Ham Hm Hq Hk.
rewrite He, (m2kb_pairs_run (ents rec) a m Ham ltac:(lia) Hq), (m2kb_pairs_key (ents rec) m kb Hm Hk).
reflexivity.
Qed.

Lemma m2kb_rop_cons : forall vf k e ps,
  Rate.rate_of_pairs vf ((k, e) :: ps) =
  (if Cursor.bytes_eqb k Rate.RATE_KEY then vf e else Rate.rate_of_pairs vf ps).
Proof.
intros vf k e ps. unfold Rate.rate_of_pairs. cbn [find fst].
destruct (Cursor.bytes_eqb k Rate.RATE_KEY); reflexivity.
Qed.

Lemma m2kb_bytes_eqb_false : forall a b, a <> b -> Cursor.bytes_eqb a b = false.
Proof.
intros a b H. destruct (Cursor.bytes_eqb a b) eqn:E; [|reflexivity].
apply Cursor.bytes_eqb_eq in E. contradiction.
Qed.

(* (b) the key is not "reac.cfg.rate": the invariant moves to m + 2, where the scan's outer head goes on *)
Lemma m2kb_inv_mismatch : forall (rec : pod_rec) (at0 m : nat) (kb : list byte),
  rsb_scan_inv rec at0 -> (at0 <= m)%nat -> (S m < length (ents rec))%nat ->
  (forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) m2kb_d) = None) ->
  key_of (nth m (ents rec) m2kb_d) = Some kb -> kb <> Rate.RATE_KEY ->
  rsb_scan_inv rec (S (S m)).
Proof.
intros rec at0 m kb Hinv Ham Hm Hq Hk Hne.
pose proof (m2kb_inv_key rec at0 m kb Hinv Ham Hm Hq Hk) as E.
split; [lia|].
rewrite E, m2kb_rop_cons, (m2kb_bytes_eqb_false kb Rate.RATE_KEY Hne). reflexivity.
Qed.

(* (a) the key is "reac.cfg.rate": the answer is the value entry's *)
Lemma m2kb_inv_match : forall (rec : pod_rec) (at0 m : nat) (kb : list byte),
  rsb_scan_inv rec at0 -> (at0 <= m)%nat -> (S m < length (ents rec))%nat ->
  (forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) m2kb_d) = None) ->
  key_of (nth m (ents rec) m2kb_d) = Some kb -> kb = Rate.RATE_KEY ->
  rsb_E0 rec = Rate.expect_value (nth (S m) (ents rec) m2kb_d).
Proof.
intros rec at0 m kb Hinv Ham Hm Hq Hk Heq. subst kb.
rewrite (m2kb_inv_key rec at0 m Rate.RATE_KEY Hinv Ham Hm Hq Hk), m2kb_rop_cons.
assert (Cursor.bytes_eqb Rate.RATE_KEY Rate.RATE_KEY = true) as -> by (apply Cursor.bytes_eqb_eq; reflexivity).
reflexivity.
Qed.

(* the value entry's type and size decide Rate.expect_value *)
Lemma m2kb_expect_int : forall e, e_type e = POD_INT -> 4 <= e_size e ->
  Rate.expect_value e = (Some (Accessors.s32 (Cursor.rd32 (e_body e))), 1).
Proof.
intros e Ht Hs. unfold Rate.expect_value, Accessors.int_of. rewrite Ht.
rewrite (proj2 (Z.leb_le 4 (e_size e)) Hs).
assert (E : (POD_INT =? POD_INT) = true) by reflexivity. rewrite E. cbn [andb]. reflexivity.
Qed.

Lemma m2kb_expect_float : forall e, e_type e = POD_FLOAT -> 4 <= e_size e ->
  Rate.expect_value e =
  match Nearest.nearest (Cursor.rd32 (e_body e)) Nearest.INT32_MIN Nearest.INT32_MAX with
  | Some n => (Some n, 1) | None => (None, -1) end.
Proof.
intros e Ht Hs. unfold Rate.expect_value, Accessors.int_of, Accessors.float_of. rewrite Ht.
rewrite (proj2 (Z.leb_le 4 (e_size e)) Hs).
assert (E1 : (POD_FLOAT =? POD_INT) = false) by reflexivity.
assert (E2 : (POD_FLOAT =? POD_FLOAT) = true) by reflexivity.
rewrite E1, E2. cbn [andb]. reflexivity.
Qed.

Lemma m2kb_expect_none : forall e,
  (e_type e <> POD_INT /\ e_type e <> POD_FLOAT) \/ e_size e < 4 ->
  Rate.expect_value e = (None, -1).
Proof.
intros e [[H1 H2]|H3]; unfold Rate.expect_value, Accessors.int_of, Accessors.float_of.
- rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
- rewrite (proj2 (Z.leb_gt 4 (e_size e)) H3).
  rewrite !andb_false_r. reflexivity.
Qed.

(* what a key entry is, and the text a NUL-terminated body holds *)
Lemma m2kb_key_of_some : forall (e : ent) (kb : list byte), key_of e = Some kb ->
  kb = Cursor.cstr (e_body e) /\ e_type e = POD_STRING /\ 1 <= e_size e /\
  bv_unsigned (nth (Z.to_nat (e_size e - 1)) (e_body e) NUL) = 0.
Proof.
intros e kb. unfold key_of, last_body_byte.
destruct (Z.eqb_spec (e_type e) POD_STRING) as [E1|E1]; cbn [andb]; cbv beta iota;
  [|intros H; discriminate H].
destruct (Z.leb_spec 1 (e_size e)) as [E2|E2]; cbn [andb]; cbv beta iota; [|intros H; discriminate H].
destruct (Z.eqb_spec (bv_unsigned (nth (Z.to_nat (e_size e - 1)) (e_body e) NUL)) 0) as [E3|E3];
  cbv beta iota; intros H; [|discriminate H].
injection H as <-. split; [reflexivity|]. split; [exact E1|]. split; [exact E2 | exact E3].
Qed.

Lemma m2kb_cstr_bytes : forall (l : list byte) (k : nat), (k < length l)%nat ->
  bv_unsigned (nth k l NUL) = 0 ->
  (length (Cursor.cstr l) < length l)%nat /\
  (forall i, (i < length (Cursor.cstr l))%nat ->
     nth i l NUL = nth i (Cursor.cstr l) NUL /\ 0 < bv_unsigned (nth i (Cursor.cstr l) NUL) < 256) /\
  bv_unsigned (nth (length (Cursor.cstr l)) l NUL) = 0.
Proof.
intros l k Hk H0.
assert (Hle : forall (l : list byte) (k : nat), (k < length l)%nat -> bv_unsigned (nth k l NUL) = 0 ->
  (Cursor.nul_idx l <= k)%nat).
{ clear. induction l as [|x l IH]; intros k; cbn [Cursor.nul_idx length]; [intros; lia|].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [Ex|Ex]; cbv beta iota; intros Hk H0; [lia|].
  destruct k as [|k]; cbn [nth] in H0; [contradiction|].
  pose proof (IH k ltac:(lia) H0). lia. }
assert (Hnz : forall (l : list byte) (i : nat), (i < Cursor.nul_idx l)%nat -> bv_unsigned (nth i l NUL) <> 0).
{ clear. induction l as [|x l IH]; intros i; cbn [Cursor.nul_idx]; [intros; lia|].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [Ex|Ex]; cbv beta iota; intros Hi; [lia|].
  destruct i as [|i]; cbn [nth]; [exact Ex|]. apply IH. lia. }
assert (Hat : forall (l : list byte), (Cursor.nul_idx l < length l)%nat ->
  bv_unsigned (nth (Cursor.nul_idx l) l NUL) = 0).
{ clear. induction l as [|x l IH]; cbn [Cursor.nul_idx length]; [intros; lia|].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [Ex|Ex]; cbv beta iota; intros Hl; cbn [nth]; [exact Ex|].
  apply IH. lia. }
assert (Hnth : forall (l : list byte) (n i : nat), (i < n)%nat -> nth i (firstn n l) NUL = nth i l NUL).
{ clear. induction l as [|x l IH]; intros n i Hi; [destruct n; reflexivity|].
  destruct n as [|n]; [lia|]. destruct i as [|i]; cbn [firstn nth]; [reflexivity|]. apply IH. lia. }
pose proof (Hle l k Hk H0) as Hn.
assert (Hlen : length (Cursor.cstr l) = Cursor.nul_idx l).
{ unfold Cursor.cstr. rewrite length_firstn. pose proof (Cursor.nul_idx_le l). lia. }
rewrite Hlen. split; [lia|]. split.
- intros i Hi. unfold Cursor.cstr. rewrite (Hnth l (Cursor.nul_idx l) i Hi). split; [reflexivity|].
  pose proof (Hnz l i Hi). pose proof (Cursor.byte_range (nth i l NUL)). lia.
- apply Hat. lia.
Qed.

Lemma m2kb_map_bv_inj : forall (a b : list byte),
  map (fun x : byte => bv_unsigned x) a = map (fun x : byte => bv_unsigned x) b -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn [map] in H; try discriminate H; [reflexivity|].
injection H as Hxy Hab. f_equal; [apply bv_eq; exact Hxy | apply IH; exact Hab].
Qed.

(* the record's bounds *)
Lemma m2kb_nent_le : forall (rec : pod_rec), pod_rec_wf rec -> (length (ents rec) <= 32)%nat.
Proof. intros rec H. exact (proj1 (ents_wf rec H)). Qed.

Lemma m2kb_ent_wf_nth : forall (rec : pod_rec) (m : nat), pod_rec_wf rec -> (m < length (ents rec))%nat ->
ent_wf (nth m (ents rec) m2kb_d).
Proof.
intros rec m Hw Hm. pose proof (proj2 (ents_wf rec Hw)) as HF.
rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hm.
Qed.

Lemma m2kb_buf_max : forall rec, pod_rec_wf rec -> Z.of_nat (length (Model.buf rec)) <= Layout.POD_BUF_MAX.
Proof.
intros rec (Hs & Hk & He & Hl & HL & Hc). unfold Model.buf, Layout.POD_BUF_MAX.
destruct (p_corr rec) as [[off bs]|].
- destruct Hc as (Ho & Hb & _). unfold Model.overwrite. rewrite !length_app, length_firstn, length_skipn. lia.
- lia.
Qed.

Lemma m2kb_bodies_96 : forall rec, pod_rec_wf rec ->
  Forall (fun e => (length (Model.e_body e) <= 96)%nat) (ents rec).
Proof.
intros rec Hw. pose proof (proj2 (ents_wf rec Hw)) as HF.
eapply Forall_impl; [|exact HF]. intros e (_ & Hb & Hs). cbv beta. lia.
Qed.

(* the entry's 104-byte image: its type, its size, and the 4 bytes at offset 8 (the body word m2kb_bw, which is
   rd32 of the body when the size is at least 4) *)
Definition m2kb_bw (e : ent) : Z := bytes_le_to_Z (rtmb_slice (Layout.ent_mem e) 8 4).

Lemma m2kb_ent_mem_len : forall e, ent_wf e -> length (Layout.ent_mem e) = 104%nat.
Proof. intros e (_ & Hb & Hs). apply Layout.length_ent_mem. lia. Qed.

Lemma m2kb_ent_type_slice : forall e, rtmb_slice (Layout.ent_mem e) 0 4 = Z_to_le_bytes 4 (e_type e).
Proof.
intros e. unfold rtmb_slice, Layout.ent_mem. cbn [skipn].
change (Z_to_le_bytes 4 (e_type e)) with (Cursor.le32 (e_type e)).
apply Layout.firstn_app_eq. reflexivity.
Qed.

Lemma m2kb_ent_size_slice : forall e, rtmb_slice (Layout.ent_mem e) 4 4 = Z_to_le_bytes 4 (e_size e).
Proof.
intros e. unfold rtmb_slice, Layout.ent_mem.
rewrite (Layout.skipn_app_eq (Cursor.le32 (e_type e))) by reflexivity.
change (Z_to_le_bytes 4 (e_size e)) with (Cursor.le32 (e_size e)).
apply Layout.firstn_app_eq. reflexivity.
Qed.

Lemma m2kb_ent_bw_slice : forall e, ent_wf e -> rtmb_slice (Layout.ent_mem e) 8 4 = Z_to_le_bytes 4 (m2kb_bw e).
Proof.
intros e He. unfold m2kb_bw.
assert (Hl : length (rtmb_slice (Layout.ent_mem e) 8 4) = 4%nat).
{ unfold rtmb_slice. rewrite length_firstn, length_skipn, (m2kb_ent_mem_len e He). reflexivity. }
pose proof (YA0d.Z_to_le_bytes_to_Z (rtmb_slice (Layout.ent_mem e) 8 4)) as HZ. rewrite Hl in HZ.
symmetry. exact HZ.
Qed.

Lemma m2kb_bw_range : forall e, ent_wf e -> 0 <= m2kb_bw e < 2 ^ 32.
Proof.
intros e He. unfold m2kb_bw.
assert (Hl : length (rtmb_slice (Layout.ent_mem e) 8 4) = 4%nat).
{ unfold rtmb_slice. rewrite length_firstn, length_skipn, (m2kb_ent_mem_len e He). reflexivity. }
pose proof (rtmb_lez_range (rtmb_slice (Layout.ent_mem e) 8 4)) as H. rewrite Hl in H. exact H.
Qed.

Lemma m2kb_bw_rd32 : forall e, ent_wf e -> 4 <= e_size e -> m2kb_bw e = Cursor.rd32 (e_body e).
Proof.
intros e (_ & Hb & Hs) H4. unfold m2kb_bw, Cursor.rd32, rtmb_slice, Layout.ent_mem.
assert (E : forall (a b : Z) (X : list byte), skipn 8 (Cursor.le32 a ++ Cursor.le32 b ++ X) = X)
  by (intros; reflexivity).
rewrite E, firstn_app.
replace (4 - length (e_body e))%nat with 0%nat by lia.
cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

(* ===================================== the engine's shadow entry over the value entry ===================================== *)
(* the five checks of this half read shadow bytes of [&ent[v], &ent[v] + 16); atom 10 holds &ent[v] at the entry
   states of the value readers, atom 20 (s4) the shadow offset *)
Definition m2kb_SH : list shent := [ mkSHE 10 0 16 ].

Section e0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the shadow entry: every byte of [a, a + 16) is marked usable and the range is apart from the shadow band *)
Lemma m2kb_sh_ok : forall (W : world rsegs) mem E a,
U E M2B_Bx = SHADOW_OFF -> U E (SOff 10 0) = a ->
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a 16 ->
(a + 16 <= kLowShadowBeg \/ kHighMemBeg <= a) ->
sh_ok rsegs M2B_Bx m2kb_SH E (mrestrict (w_H W) mem).
Proof.
intros W mem E a HB H10 Hra Happ. apply Forall_cons; [|apply Forall_nil].
apply (YCbq.shent_ok_of_range rsegs (w_H W) mem E M2B_Bx 10 a 16 a 0 16 Hra HB H10 ltac:(lia) ltac:(lia)).
intros x Hx. cbn [Z.min Z.max] in Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
End e0.

(* ===================================== the cut lists and the interfaces of the pieces ===================================== *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the value entry e at a0v in a state's view: its type, size and body word, its 16 bytes marked usable, inside the
   allocator's range and apart from the shadow band *)
Definition m2kb_ent_facts (W : world rsegs) (mem : word -> option byte) (e : ent) (a0v : Z) : Prop :=
ent_wf e /\
val_mem rsegs (mrestrict (w_H W) mem) a0v 4 (e_type e) /\
val_mem rsegs (mrestrict (w_H W) mem) (a0v + 4) 4 (e_size e) /\
val_mem rsegs (mrestrict (w_H W) mem) (a0v + 8) 4 (m2kb_bw e) /\
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a0v 16 /\
4096 <= a0v /\ a0v + 16 <= alloc_ceiling /\ (a0v + 16 <= kLowShadowBeg \/ kHighMemBeg <= a0v).

(* the model side of the match: the answer is the value entry's, and the parse's answer is the scan's *)
Definition m2kb_match (cx : rsb_scx rsegs) (rec : pod_rec) (e : ent) : Prop :=
rsb_E0 rec = Rate.expect_value e /\ snd (rsb_PA rsegs cx rec) = snd (rsb_E0 rec) /\
fst (rsb_PA rsegs cx rec) = fst (rsb_E0 rec).

(* the address of ent[v] *)
Definition m2kb_ea (cx : rsb_scx rsegs) (v : nat) : Z := q_pp (x_e rsegs cx) + 0x4014 + 104 * Z.of_nat v.

(* the two cells A's cut carries beyond rsb_L_chk: F in R+0x60 and pp in R+0x168 *)
Definition m2kb_L_FP (cx : rsb_scx rsegs) : list (rt_loc * Z) :=
[(LCell XR 0x60, q_F (x_e rsegs cx)); (LCell XR 0x168, q_pp (x_e rsegs cx))].

(* KV 0x82c98: the key matched; a0 = &ent[v], a7 = &ent[0] + 4, s8 = 104 v, s7 = the flags byte (0x82c8c), and the
   cells the readers load: F, pp, the code (R+0x170) and 0x4018 (R+0x138) *)
Definition m2kb_L_val (cx : rsb_scx rsegs) (rec : pod_rec) (v : nat) : list (rt_loc * Z) :=
[(LReg 10, m2kb_ea cx v); (LReg 17, q_pp (x_e rsegs cx) + 0x4018); (LReg 24, 104 * Z.of_nat v);
 (LReg 23, q_fl (x_e rsegs cx))] ++ m2kb_L_FP cx ++
[(LCell XR 0x170, snd (rsb_PA rsegs cx rec)); (LCell XR 0x138, 0x4018)].
Definition m2kb_K_val (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec) : Prop :=
forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3 (e : ent) (v : nat),
rsb_chk_base (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ->
rsb_hz_at rsegs cx rec W3 mem3 ->
rsb_at_cx rsegs cx W3 mem3 regs3 (rsb_L_chk rsegs cx ++ m2kb_L_val cx rec v) ->
(v <= 32)%nat -> m2kb_ent_facts W3 mem3 e (m2kb_ea cx v) -> m2kb_match cx rec e ->
SRr rsegs W3 (@cfg_at fx3 rsegs M2B_KV regs3 mem3 md3) POST.

(* FLT 0x82d70: A's cut holds (s10 = the code, s6 = the mask, s7 = the flags byte), a0 = &ent[v], a7, s8, a4 = pp
   (0x82cb4) and R+0x138 = 0x4018 as at KV, type 6 *)
Definition m2kb_L_flt (cx : rsb_scx rsegs) (v : nat) : list (rt_loc * Z) :=
[(LReg 10, m2kb_ea cx v); (LReg 17, q_pp (x_e rsegs cx) + 0x4018); (LReg 24, 104 * Z.of_nat v);
 (LReg 14, q_pp (x_e rsegs cx)); (LCell XR 0x138, 0x4018)].
Definition m2kb_K_float (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec) : Prop :=
forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3 (e : ent) (v : nat),
rsb_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ->
rsb_at_cx rsegs cx W3 mem3 regs3 (m2kb_L_flt cx v) ->
(v <= 32)%nat -> m2kb_ent_facts W3 mem3 e (m2kb_ea cx v) -> e_type e = POD_FLOAT -> m2kb_match cx rec e ->
SRr rsegs W3 (@cfg_at fx3 rsegs M2KB_FLT regs3 mem3 md3) POST.

(* JN 0x82dd0: A's cut holds, the answer is a rate, and a2 holds the value as a sign-extended 32-bit word (the value
   the hz cell holds) *)
Definition m2kb_K_join (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec) : Prop :=
forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3,
rsb_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ->
snd (rsb_PA rsegs cx rec) = 1 ->
getr regs3 (Z_to_bv 5 12) = w64 (m2kb_sx (rsb_hz rsegs cx rec mod 2 ^ 32)) ->
SRr rsegs W3 (@cfg_at fx3 rsegs M2KB_JN regs3 mem3 md3) POST.

(* the four pieces, each one stretch of code between the pcs above; m2kb_chain chains them *)
(* JN 0x82dd0 -> A: a1 := the hz cell, a0 := s10, check_rate, j A *)
Definition m2kb_join_stmt : Prop :=
forall (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec),
rsb_pre rsegs B cx -> rsb_from_A (fx := fx) rsegs B MT cx POST -> m2kb_K_join cx POST rec.
(* FLT 0x82d70 -> MAL / JN: the size, the body, the flw, pod_nearest, the out cell *)
Definition m2kb_float_stmt : Prop :=
forall (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec),
rsb_pre rsegs B cx -> rsb_from_MAL (fx := fx) rsegs B MT cx POST -> m2kb_K_join cx POST rec ->
m2kb_K_float cx POST rec.
(* KV 0x82c98 -> FLT / MAL / JN: the type, s6 / a4 / s10, the Int arm *)
Definition m2kb_val_stmt : Prop :=
forall (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec),
rsb_pre rsegs B cx -> rsb_from_MAL (fx := fx) rsegs B MT cx POST -> m2kb_K_float cx POST rec ->
m2kb_K_join cx POST rec -> m2kb_K_val cx POST rec.
(* KM 0x82c40 -> O / KV: the trap and the dead `bltz`, the spills, the strcmp wrapper, the reloads, the mismatch
   exit, the two value traps, &ent[v] *)
Definition m2kb_key_stmt : Prop :=
forall (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (inp : list byte) (at0 m : nat),
rsb_start_M02 (fx := fx) rsegs B cx inp -> rsb_from_O (fx := fx) rsegs B MT cx POST (S (S m)) ->
(forall rec, m2kb_K_val cx POST rec) -> rsb_from_KM (fx := fx) rsegs B MT cx POST at0 m.
End i.

(* ===================================== the chain of the four pieces ===================================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* KM -> (O | KV); KV -> (FLT | MAL | JN); FLT -> (MAL | JN); JN -> A *)
Lemma m2kb_chain : m2kb_join_stmt B MT -> m2kb_float_stmt B MT -> m2kb_val_stmt B MT -> m2kb_key_stmt B MT ->
rsb_piece_W11b_key_stmt rsegs B MT.
Proof.
intros HJ HF HV HK. unfold rsb_piece_W11b_key_stmt.
intros cx POST inp at0 m Hst HO _ HMAL HA.
pose proof Hst as (Hpre & _).
apply (HK cx POST inp at0 m Hst HO). intros rec.
apply (HV cx POST rec Hpre HMAL).
- exact (HF cx POST rec Hpre HMAL (HJ cx POST rec Hpre HA)).
- exact (HJ cx POST rec Hpre HA).
Qed.
End a.

(* ===================================== registers kept across a cut ===================================== *)
(* the registers rsb_L_chk names: s0, s1, s3, s4, s5, all callee-saved; chb_L adds sp *)
Definition m2kb_L5 : list (bv 5) := [8; 9; 19; 20; 21]%bv.
Definition chb_L : list (bv 5) := [2; 8; 9; 19; 20; 21]%bv.
Lemma m2kb_L5_cs : forall r, In r m2kb_L5 -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [m2kb_L5 In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
Lemma chb_L_cs : forall r, In r chb_L -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [chb_L In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
Lemma m2kb_cs_sub : forall (L1 L2 : list (bv 5)) ra rb, (forall r, In r L1 -> In r L2) -> cs_eq L2 ra rb -> cs_eq L1 ra rb.
Proof. intros L1 L2 ra rb HS H r Hr. exact (H r (HS r Hr)). Qed.
Lemma m2kb_L5_chb : forall r, In r m2kb_L5 -> In r chb_L.
Proof. intros r Hr. cbv [m2kb_L5 chb_L In] in Hr |- *. tauto. Qed.
(* a register of a kept list, read through it *)
Ltac m2kb_get Hcs r :=
etransitivity; [exact (Hcs r ltac:(cbv [m2kb_L5 chb_L In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].

(* ===================================== the cut facts across a call or a run ===================================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the first block and the frame for locals lie below the allocator's ceiling, which lies below the callees'
   stack; the first block lies apart from the shadow band *)
Lemma m2kb_apart : forall cx : rsb_scx rsegs, rsb_pre rsegs B cx ->
4096 <= q_pp (x_e rsegs cx) /\ q_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling /\
(q_pp (x_e rsegs cx) + Layout.PP_SIZE <= kLowShadowBeg \/ kHighMemBeg <= q_pp (x_e rsegs cx)) /\
4096 <= q_F (x_e rsegs cx) /\ q_F (x_e rsegs cx) + 1024 <= alloc_ceiling /\
alloc_ceiling <= q_R (x_e rsegs cx) - T_SEG_STK /\ 2 ^ 46 <= q_R (x_e rsegs cx) <= 2 ^ 47.
Proof.
intros cx Hpre. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2b_stack B cx Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
pose proof (m2b_frameF B cx Hpre) as (_ & HF0 & HFc & _ & _).
pose proof Hpre as Hpre'. unfold rsb_pre, rt_seg_pre in Hpre'.
destruct Hpre' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hppin & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hppin) as (_ & Hp0 & Hpc & Happ & _).
assert (Hreq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
rewrite Hreq in Hpc, Happ.
unfold in_app in Happ. destruct Happ as (_ & Happ').
split; [lia|]. split; [lia|].
split; [destruct Happ' as [H|[H _]]; [left; exact H | right; exact H]|].
split; [lia|]. split; [lia|]. split; [lia | exact H46].
Qed.

(* the bytes the match half (its runs and its callees) may change: the callees' stack below R, the four spill
   cells R+0x140 (t2), R+0x150 (t1), R+0x158 (t0), R+0x160 (a7) and pod_nearest's out cell R+0x198 *)
Definition m2kb_wz (cx : rsb_scx rsegs) (a : Z) : Prop :=
(q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) \/
(q_R (x_e rsegs cx) + 0x140 <= a < q_R (x_e rsegs cx) + 0x148) \/
(q_R (x_e rsegs cx) + 0x150 <= a < q_R (x_e rsegs cx) + 0x168) \/
(q_R (x_e rsegs cx) + 0x198 <= a < q_R (x_e rsegs cx) + 0x1a0).

(* the zone lies in the callees' stack or in M02's write set *)
Lemma m2kb_wz_E2 : forall cx : rsb_scx rsegs, forall a, m2kb_wz cx a ->
(q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) \/ rsb_E2 rsegs cx a.
Proof.
intros cx a [H|[H|[H|H]]]; [left; exact H | | |]; right; left;
unfold rt_inw; cbn [hi_w2 rate_himg_B]; rewrite !Exists_cons; cbn [rt_xv fst snd]; lia.
Qed.

(* a byte below the allocator's ceiling is outside that zone *)
Lemma m2kb_far_low : forall cx : rsb_scx rsegs, rsb_pre rsegs B cx -> forall a, 0 <= a < alloc_ceiling ->
0 <= a < 2 ^ 64 /\ ~ m2kb_wz cx a.
Proof.
intros cx Hpre a Ha. pose proof (m2kb_apart cx Hpre) as (_ & _ & _ & _ & _ & Hc & H46).
pose proof asan_consts as (C1 & _). unfold m2kb_wz, T_SEG_STK, ASTACK in *. lia.
Qed.

(* a real-frame cell [R + o, R + o + 8) apart from the spill cells and the out cell is outside that zone *)
Lemma m2kb_far_cell : forall cx : rsb_scx rsegs, rsb_pre rsegs B cx -> forall o k,
0 <= o -> o + 8 <= 0x220 -> 0 <= k < 8 ->
(o + 8 <= 0x140 \/ (0x148 <= o /\ o + 8 <= 0x150) \/ (0x168 <= o /\ o + 8 <= 0x198) \/ 0x1a0 <= o) ->
0 <= q_R (x_e rsegs cx) + o + k < 2 ^ 64 /\ ~ m2kb_wz cx (q_R (x_e rsegs cx) + o + k).
Proof.
intros cx Hpre o k Ho Ho8 Hk Hz. pose proof (m2kb_apart cx Hpre) as (_ & _ & _ & _ & _ & Hc & H46).
unfold m2kb_wz, T_SEG_STK, ASTACK in *. lia.
Qed.

Lemma chb_garr8_kept : forall H H' (m m' : word -> option byte) a l,
garr8 rsegs (mrestrict H m) a l ->
(forall j, (j < length l)%nat -> aview rsegs H' m' (a + Z.of_nat j) = aview rsegs H m (a + Z.of_nat j)) ->
garr8 rsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l G K j Hj. destruct (G j Hj) as (Hv & Hr). split; [|exact Hr].
eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. change (Z.of_nat 1) with 1 in Hk.
replace k with 0 by lia. rewrite Z.add_0_r. exact (K j Hj).
Qed.

(* rsb_chk_base and the hz cell, carried to a state whose memory agrees outside m2kb_wz, at a float state that
   keeps every float register outside fa0, fa3, fa4, fa5 *)
Lemma m2kb_base_kept : forall (cx : rsb_scx rsegs) (fx2 fx3 : YK11.FPState) rec
ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rsb_pre rsegs B cx -> rsb_chk_base (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rsb_hz_at rsegs cx rec W2 mem2 ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> rt_fxk [10; 13; 14; 15] fx fx3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ m2kb_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rsb_chk_base (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 /\ rsb_hz_at rsegs cx rec W3 mem3.
Proof.
intros cx fx2 fx3 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre
(Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1) Hhz Hcore3 Hfxk3 K3.
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof (m2b_pp B cx Hpre) as (P4096 & Pceil & _).
pose proof (m2kb_far_low cx Hpre) as Far.
pose proof ck_segs_low as Hsegs. pose proof asan_consts as (C1 & _).
split.
- split; [exact Hcore3|]. split; [exact Hfxk3|].
  split.
  { apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ Hfsh). intros i Hi.
    assert (Hlen88 : Z.of_nat (length rsb_PB) = 88) by (vm_compute; reflexivity). rewrite Hlen88 in Hi.
    assert (Hsh : 0 <= shadow_addr (q_F (x_e rsegs cx)) + i < alloc_ceiling).
    { unfold shadow_addr, SHADOW_OFF.
      pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (q_F (x_e rsegs cx)) 8 ltac:(lia)) as M.
      assert (0 <= q_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
      lia. }
    destruct (Far _ Hsh) as (Hb & Hs). apply K3; assumption. }
  split.
  { eapply (rtmb_rom_kept rsegs); [exact Hrom|]. intros a (sg & Hsg & _ & Hr).
    pose proof (Hsegs a ltac:(exists sg; split; [exact Hsg | exact Hr])) as Hl. unfold kLowMemEnd in Hl.
    destruct (Far a ltac:(lia)) as (Hb & Hs). apply K3; assumption. }
  split.
  { unfold rsb_pp_at in *. apply (chb_garr8_kept _ _ _ _ _ _ Hpp). intros j Hj.
    unfold rsb_u8s in Hj. rewrite length_map in Hj. pose proof (Layout.length_pp_bytes rec Hwf) as HL0.
    destruct (Far (q_pp (x_e rsegs cx) + Z.of_nat j) ltac:(lia)) as (Hb & Hs). apply K3; assumption. }
  split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hpod0|]. split; [exact Hpod | exact Hpod1].
- unfold rsb_hz_at in *. eapply (val_mem_kept rsegs); [|exact Hhz]. intros k Hk. change (Z.of_nat 4) with 4 in Hk.
  destruct (Far (q_F (x_e rsegs cx) + 0x2a0 + k) ltac:(lia)) as (Hb & Hs). apply K3; assumption.
Qed.

(* a real-frame cell apart from the spill cells and the out cell, carried the same way *)
Lemma m2kb_cell_kept : forall (cx : rsb_scx rsegs) (W2 : world rsegs) mem2 (W3 : world rsegs) mem3 o v,
rsb_pre rsegs B cx -> 0 <= o -> o + 8 <= 0x220 ->
(o + 8 <= 0x140 \/ (0x148 <= o /\ o + 8 <= 0x150) \/ (0x168 <= o /\ o + 8 <= 0x198) \/ 0x1a0 <= o) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ m2kb_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + o) 8 v ->
val_mem rsegs (mrestrict (w_H W3) mem3) (q_R (x_e rsegs cx) + o) 8 v.
Proof.
intros cx W2 mem2 W3 mem3 o v Hpre Ho Ho8 Hz K3 Hv.
eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
destruct (m2kb_far_cell cx Hpre o k Ho Ho8 Hk Hz) as (Hb & Hs). apply K3; assumption.
Qed.

(* rsb_L_chk's facts, carried to a state whose registers s0, s1, s3, s4, s5 (m2kb_L5) agree and whose memory
   agrees outside m2kb_wz *)
Lemma m2kb_chk_kept : forall (cx : rsb_scx rsegs) W2 mem2 regs2 W3 mem3 regs3,
rsb_pre rsegs B cx ->
rsb_at_cx rsegs cx W2 mem2 regs2 (rsb_L_chk rsegs cx) -> cs_eq m2kb_L5 regs2 regs3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ m2kb_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rsb_at_cx rsegs cx W3 mem3 regs3 (rsb_L_chk rsegs cx).
Proof.
intros cx W2 mem2 regs2 W3 mem3 regs3 Hpre Hat HL K3.
unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc in Hat. rewrite Forall_app, !Forall_cons_iff in Hat.
destruct Hat as ((A8 & A9 & A19 & A20 & AC178 & A21 & AC10 & AC50 & _) &
                 (AC48 & AC30 & AC38 & AC40 & AC18 & AC148 & _)).
cbn [rt_at rt_xv fst snd] in A8, A9, A19, A20, AC178, A21, AC10, AC50, AC48, AC30, AC38, AC40, AC18, AC148.
unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc. cbn [app].
repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
- m2kb_get HL (8%bv : bv 5). exact A8.
- m2kb_get HL (9%bv : bv 5). exact A9.
- m2kb_get HL (19%bv : bv 5). exact A19.
- m2kb_get HL (20%bv : bv 5). exact A20.
- apply (m2kb_cell_kept cx W2 mem2 W3 mem3 0x178); [exact Hpre | lia | lia | lia | exact K3 | exact AC178].
- m2kb_get HL (21%bv : bv 5). exact A21.
- apply (m2kb_cell_kept cx W2 mem2 W3 mem3 0x10); [exact Hpre | lia | lia | lia | exact K3 | exact AC10].
- apply (m2kb_cell_kept cx W2 mem2 W3 mem3 0x50); [exact Hpre | lia | lia | lia | exact K3 | exact AC50].
- apply (m2kb_cell_kept cx W2 mem2 W3 mem3 0x48); [exact Hpre | lia | lia | lia | exact K3 | exact AC48].
- apply (m2kb_cell_kept cx W2 mem2 W3 mem3 0x30); [exact Hpre | lia | lia | lia | exact K3 | exact AC30].
- apply (m2kb_cell_kept cx W2 mem2 W3 mem3 0x38); [exact Hpre | lia | lia | lia | exact K3 | exact AC38].
- apply (m2kb_cell_kept cx W2 mem2 W3 mem3 0x40); [exact Hpre | lia | lia | lia | exact K3 | exact AC40].
- apply (m2kb_cell_kept cx W2 mem2 W3 mem3 0x18); [exact Hpre | lia | lia | lia | exact K3 | exact AC18].
- apply (m2kb_cell_kept cx W2 mem2 W3 mem3 0x148); [exact Hpre | lia | lia | lia | exact K3 | exact AC148].
Qed.

(* A's cut at a later state: from the facts of a cut of the half (rsb_chk_base, the hz cell, rsb_L_chk and the two
   cells R+0x60 = F, R+0x168 = pp), the registers s0, s1, s3, s4, s5 as there, s10 = the answer's code, s6 = the
   mask, s7 = the flags byte, the memory as there outside m2kb_wz, and the float state kept outside fa0, fa3, fa4,
   fa5 *)
Lemma m2kb_cut_A : forall (cx : rsb_scx rsegs) (fx2 fx3 : YK11.FPState) rec
ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rsb_pre rsegs B cx -> rsb_chk_base (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rsb_hz_at rsegs cx rec W2 mem2 ->
rsb_at_cx rsegs cx W2 mem2 regs2 (rsb_L_chk rsegs cx ++ m2kb_L_FP cx) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> rt_fxk [10; 13; 14; 15] fx fx3 ->
cs_eq m2kb_L5 regs2 regs3 ->
getr regs3 (Z_to_bv 5 26) = w64 (snd (rsb_PA rsegs cx rec)) ->
getr regs3 (Z_to_bv 5 22) = w64 (q_mask (x_e rsegs cx)) ->
getr regs3 (Z_to_bv 5 23) = w64 (q_fl (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ m2kb_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rsb_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx fx2 fx3 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hhz Hat Hcore3 Hfxk3
HL H26 H22 H23 K3.
destruct (m2kb_base_kept cx fx2 fx3 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hhz Hcore3
  Hfxk3 K3) as (Hbase3 & Hhz3).
assert (HatL : rsb_at_cx rsegs cx W2 mem2 regs2 (rsb_L_chk rsegs cx)).
{ unfold rsb_at_cx, rsb_at in Hat |- *. rewrite Forall_app in Hat. exact (proj1 Hat). }
pose proof (m2kb_chk_kept cx W2 mem2 regs2 W3 mem3 regs3 Hpre HatL HL K3) as HatL3.
unfold rsb_at_cx, rsb_at, m2kb_L_FP in Hat. rewrite Forall_app, !Forall_cons_iff in Hat.
destruct Hat as (_ & AC60 & AC168 & _). cbn [rt_at rt_xv fst snd] in AC60, AC168.
split; [exact Hbase3|]. split; [|exact Hhz3].
unfold rsb_at_cx, rsb_at in HatL3 |- *. rewrite Forall_app. split; [exact HatL3|].
repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
- exact H26.
- exact H22.
- exact H23.
- apply (m2kb_cell_kept cx W2 mem2 W3 mem3 0x60); [exact Hpre | lia | lia | lia | exact K3 | exact AC60].
- apply (m2kb_cell_kept cx W2 mem2 W3 mem3 0x168); [exact Hpre | lia | lia | lia | exact K3 | exact AC168].
Qed.

(* the same at the float state of the cut, from a state whose memory agrees outside the callees' stack and whose
   registers of chb_L agree [A's ch_cut_A] *)
Lemma chb_cut_A : forall (cx : rsb_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rsb_pre rsegs B cx -> rsb_chk_base (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rsb_at_cx rsegs cx W2 mem2 regs2 (rsb_L_chk rsegs cx ++ m2kb_L_FP cx) -> rsb_hz_at rsegs cx rec W2 mem2 ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq chb_L regs2 regs3 ->
getr regs3 (Z_to_bv 5 26) = w64 (snd (rsb_PA rsegs cx rec)) ->
getr regs3 (Z_to_bv 5 22) = w64 (q_mask (x_e rsegs cx)) ->
getr regs3 (Z_to_bv 5 23) = w64 (q_fl (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rsb_cut_A (fx := fx) rsegs B MT cx fx2 rec ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hat Hhz Hcore3 HL H26 H22 H23 K3.
pose proof Hbase as (_ & Hfxk & _).
apply (m2kb_cut_A cx fx2 fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hhz Hat Hcore3
  Hfxk (m2kb_cs_sub _ _ _ _ m2kb_L5_chb HL) H26 H22 H23).
intros a Ha Hz. apply K3; [exact Ha|]. intros Hs. apply Hz. left. exact Hs.
Qed.

(* MAL's cut is A's when the answer is (None, -1) *)
Lemma m2kb_mal_of_A : forall (cx : rsb_scx rsegs) (fx3 : YK11.FPState) rec ly3 S3 W3 regs3 mem3 md3,
rsb_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ->
fst (rsb_PA rsegs cx rec) = None -> snd (rsb_PA rsegs cx rec) = -1 ->
rsb_cut_MAL (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (Hb & Ha & Hh) Hn Hm.
rewrite Hm in Ha. split; [exact Hb|]. split; [exact Ha|]. split; [exact Hh|]. split; [exact Hn | exact Hm].
Qed.

(* the value entry ent[v] at a state of the half: its facts at &ent[v] = pp + 0x4014 + 104 v *)
Lemma m2kb_ent_at : forall (cx : rsb_scx rsegs) (fx2 : YK11.FPState) rec ly2 S2 W2 regs2 mem2 md2 (v : nat),
rsb_pre rsegs B cx -> rsb_chk_base (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
(v < length (ents rec))%nat ->
m2kb_ent_facts W2 mem2 (nth v (ents rec) m2kb_d) (m2kb_ea cx v).
Proof.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 v Hpre
(Hcore & _ & _ & _ & Hpp & Hwf & _) Hv.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2kb_apart cx Hpre) as (Hp0 & Hpc & Happ & _).
pose proof (m2kb_nent_le rec Hwf) as Hn32.
pose proof (m2kb_ent_wf_nth rec v Hwf Hv) as Hewf.
set (e := nth v (ents rec) m2kb_d).
unfold m2kb_ea. set (a := q_pp (x_e rsegs cx) + 0x4014 + 104 * Z.of_nat v).
assert (B0 : rtmb_bytes rsegs (w_H W2) mem2 (q_pp (x_e rsegs cx)) (Layout.pp_bytes rec)) by exact Hpp.
unfold Layout.pp_bytes in B0.
pose proof (rtmb_pp_ent rsegs (Model.buf rec) (Model.is_props rec) (Model.has_params rec)
  (Model.params_struct rec) (Model.ents rec) (Model.corrupt rec) (m2kb_buf_max rec Hwf) Hn32
  (m2kb_bodies_96 rec Hwf) (w_H W2) mem2 (q_pp (x_e rsegs cx)) v B0 Hv) as BE.
change (Model.Ent 0 0 []) with m2kb_d in BE. fold e in BE.
replace (q_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat v)) with a in BE
  by (unfold a, Layout.OFF_ENT, Layout.ENT_SIZE; lia).
pose proof (m2kb_ent_mem_len e Hewf) as HL.
assert (HAR : AR rsegs B ly2 S2 W2 mem2 md2) by exact (proj1 (proj1 Hcore)).
assert (Hin : In (q_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2)).
{ pose proof Hpre as Hp. unfold rsb_pre, rt_seg_pre in Hp.
  destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hppin & _).
  destruct Hcore as (_ & _ & _ & Hperm & _).
  apply (Permutation_in _ (Permutation_sym Hperm)). exact Hppin. }
assert (Hreq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
unfold Layout.PP_SIZE in *.
split; [exact Hewf|].
split.
{ replace a with (a + Z.of_nat 0) by lia.
  apply (rtmb_bytes_field rsegs (w_H W2) mem2 a (Layout.ent_mem e) 0 4); [exact BE | apply m2kb_ent_type_slice | lia]. }
split.
{ replace (a + 4) with (a + Z.of_nat 4) by lia.
  apply (rtmb_bytes_field rsegs (w_H W2) mem2 a (Layout.ent_mem e) 4 4); [exact BE | apply m2kb_ent_size_slice | lia]. }
split.
{ replace (a + 8) with (a + Z.of_nat 8) by lia.
  apply (rtmb_bytes_field rsegs (w_H W2) mem2 a (Layout.ent_mem e) 8 4);
  [exact BE | apply (m2kb_ent_bw_slice e Hewf) | lia]. }
split.
{ refine (proj1 (rtmb_blk_ra rsegs B ly2 S2 W2 mem2 md2 (q_pp (x_e rsegs cx)) 19744 a 16 HAR Hin _ _));
  unfold a; rewrite ?Hreq; lia. }
unfold a. split; [lia|]. split; [lia|]. destruct Happ as [H|H]; [left | right]; lia.
Qed.
End c.

(* ===================================== helpers of the walks ===================================== *)
(* an extra env slot's denotation *)
Lemma m2kb_den_extra : forall regs extra (j : nat) v, nth j extra (Z_to_bv 64 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot (Ereg regs extra) (SOff (32 + j) 0) = Z_to_bv 64 v.
Proof.
intros regs extra j v Hn Hv. apply bv_eq. rewrite denot_SOff, Z.add_0_r, ew_Ereg_extra, Hn.
rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the value entry's facts in a view that agrees everywhere *)
Lemma m2kb_ent_facts_kept : forall (W W' : world rsegs) mem mem' e a0v,
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W') mem' a = aview rsegs (w_H W) mem a) ->
m2kb_ent_facts W mem e a0v -> m2kb_ent_facts W' mem' e a0v.
Proof.
intros W W' mem mem' e a0v K (Hewf & Hvt & Hvs & Hvb & Hra & H0 & H1 & Happ).
pose proof (@YM05.alloc_ceiling_lt rc) as Hc0.
assert (K16 : forall k, 0 <= k < 16 -> aview rsegs (w_H W') mem' (a0v + k) = aview rsegs (w_H W) mem (a0v + k))
by (intros k Hk; apply K; lia).
split; [exact Hewf|].
split; [eapply (val_mem_kept rsegs); [|exact Hvt]; intros k Hk; change (Z.of_nat 4) with 4 in Hk; apply K16; lia|].
split; [eapply (val_mem_kept rsegs); [|exact Hvs]; intros k Hk; change (Z.of_nat 4) with 4 in Hk;
  replace (a0v + 4 + k) with (a0v + (4 + k)) by lia; apply K16; lia|].
split; [eapply (val_mem_kept rsegs); [|exact Hvb]; intros k Hk; change (Z.of_nat 4) with 4 in Hk;
  replace (a0v + 8 + k) with (a0v + (8 + k)) by lia; apply K16; lia|].
split.
{ apply (rtmb_ra_kept rsegs (w_H W) mem (w_H W') mem' SHADOW_OFF a0v 16 Hra). intros x Hx. apply K.
  unfold shadow_of_addr, SHADOW_OFF.
  assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
split; [exact H0|]. split; [exact H1 | exact Happ].
Qed.
End e.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* A's cut after a run of the engine (no byte changed) from a state with the facts of a cut of the half: the
   registers of rsb_L_chk kept, s10 = the answer's code, s6 = the mask and s7 = the flags byte *)
Lemma m2kb_run_A : forall (cx : rsb_scx rsegs) (fx3 : YK11.FPState) rec ly3 S3 W3 regs3 mem3 md3 regsN memN mdN,
rsb_pre rsegs B cx ->
rsb_chk_base (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 -> rsb_hz_at rsegs cx rec W3 mem3 ->
rsb_at_cx rsegs cx W3 mem3 regs3 (rsb_L_chk rsegs cx ++ m2kb_L_FP cx) ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 memN mdN (x_k rsegs cx) ->
same_io md3 mdN -> cs_eq [2; 3; 4]%bv regs3 regsN -> cs_eq m2kb_L5 regs3 regsN ->
getr regsN (Z_to_bv 5 26) = w64 (snd (rsb_PA rsegs cx rec)) ->
getr regsN (Z_to_bv 5 22) = w64 (q_mask (x_e rsegs cx)) ->
getr regsN (Z_to_bv 5 23) = w64 (q_fl (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W3) memN a = aview rsegs (w_H W3) mem3 a) ->
rsb_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regsN memN mdN.
Proof using MTL.
intros cx fx3 rec ly3 S3 W3 regs3 mem3 md3 regsN memN mdN Hpre Hbase Hhz Hat HJ Hio C234 CL5 H26 H22 H23 K.
pose proof Hbase as (Hcore & Hfxk & _).
assert (HcoreN : rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W3 regsN memN mdN).
{ apply (m2b_core_step B MT MTL cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 regsN memN mdN Hcore HJ);
  [ intros r Hr; apply C234; cbv [In];
    destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
  | reflexivity | apply Permutation_refl | exact Hio | apply (mo_le_refl MT MTL) |].
  intros a Ha _ _. exact (K a Ha). }
exact (m2kb_cut_A B MT cx fx3 fx3 rec ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 regsN memN mdN Hpre Hbase Hhz Hat
  HcoreN Hfxk CL5 H26 H22 H23 (fun a Ha _ => K a Ha)).
Qed.
End w.

Print Assumptions m2kb_chain.
Print Assumptions m2kb_cut_A.
Print Assumptions chb_cut_A.
Print Assumptions m2kb_ent_at.
Print Assumptions m2kb_run_A.
