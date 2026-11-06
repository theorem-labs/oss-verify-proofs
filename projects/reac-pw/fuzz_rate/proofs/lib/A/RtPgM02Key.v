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
(* reac-pw/fuzz_rate, image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, the same loaded bytes). Proves no function
   (kind: segment lemma): rt_m02_key_A, lib/A/RtPgSeg.v's rs_piece_W11b_key_stmt, the key compare and the value
   readers of LLVMFuzzerTestOneInput's segment M02, from the cut KM 0x82aac to O 0x829c0 (the key is not
   "reac.cfg.rate": at = m + 2), ABS 0x82b7c (dead), MAL 0x82c9c (the value is not a rate) or A 0x82ca8 (check_rate
   ran). lib/A/RtPgM02Base.v holds the code table, the regions and the callee seam; nothing here restates a cut.

   THE CODE (lib/A/RtPgM02Base.v lists it with every pc):
     KM  0x82aac .. 0x82ad4  m := s6 - 1; the dead `blt` to ABS; a1 := 0x20fa0; four spills to R+0x110 .. R+0x130;
                             jal the strcmp wrapper 0x4219c (a0 = &ent[m].body)
         0x82ad8 .. 0x82afc  the reloads; bnez a0 -> O with a1 = m + 2
         0x82b00 .. 0x82b10  a0 := &ent[v], v = m + 1
     KV  0x82b14 .. 0x82b3c  the type's check, s6 := F, s10 := the flags byte, Float 6 -> 0x82c44, not Int 4 -> MAL
     Int 0x82b40 .. 0x82b78  the size's check, size < 4 -> MAL, the body word into a2, j JN
     FLT 0x82c44 .. 0x82c88  the size's check, size < 4 -> MAL, flw fa0 (the body word), pod_nearest(fa0,
                             R+0x158), None -> MAL, the out cell's low word into a2
     JN  0x82c8c .. 0x82c98  a1 := the hz cell, a0 := s8, jal check_rate, j A.
   The pieces below are stated in continuation form (m2k_K_val, m2k_K_float, m2k_K_join) so each is one lemma about
   one stretch of code; m2k_chain chains them and rt_m02_key_A at the end applies it.

   SECTION HYPOTHESES of rt_m02_key_A: MTL : ameter_laws MT; HGOT : as_got_shadow B = 0x9be70 and
   HSC : as_shadow_cell B = 0xa4c38 (the runtime symbol record's two cells pod_nearest's code reads; with them
   lib/A/RtPgNearA.v's rt_pod_nearest_A gives pod_nearest's contract at every float state, m2k_near); and
   ASTRCMP : forall fy, astrcmp_realizes (fx := fy) rsegs B M2_STRCMP (the strcmp wrapper's contract at every float
   state, lib/Reusable/AStrcmpDef.v). The frame's laws come from the kernel theorem YG0q.AR_laws_ok. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Nearest Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSiteA RtPgSeg RtPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgCheck RtPgStrcmp RtPgM02Base RtPgM02Chk.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgNearC RtPgNearA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ===================================== the pcs the pieces meet at ===================================== *)
Definition M2K_KV : Z := 0x82b14.       (* the value entry's address is formed: srli a1,a0,3 *)
Definition M2K_FLT : Z := 0x82c44.      (* the Float arm: addi a1,a0,4 *)
Definition M2K_JN : Z := 0x82c8c.       (* the two arms meet: lw a1,0(s5) *)

(* ===================================== the value language ===================================== *)
(* m2k_denot_a0 / m2k_U_a0: the address of ent[v] that 0x82b00 .. 0x82b10 forms, `li a0,13; slli a0,a0,35;
   slli s6,s6,32; mulhu a0,s6,a0; add a0,t2,a0`: mulhu((v * 2^32) mod 2^64, 13 * 2^35) = 104 v for 0 <= v <= 32,
   since (v * 2^32) * (13 * 2^35) = 104 v * 2^64. m2k_sx and its lemmas: the 64-bit word an `lw` leaves for a
   32-bit pattern. *)
Lemma m2k_denot_a0 : forall E (n p : nat) (i b : Z),
  ew E n = Z_to_bv 64 i -> 0 <= i <= 32 ->
  ew E p = Z_to_bv 64 b -> 0 <= b -> b + 104 * i < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff p 0)
                (SMd M_MULHU (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 446676598784)))
  = Z_to_bv 64 (b + 104 * i).
Proof.
intros E n p i b Hn Hi Hp Hb Hs.
rewrite (denot_lit_U E). apply (f_equal (Z_to_bv 64)).
rewrite ?U_SAlu, ?U_SMd, ?U_SAlu, ?U_SOff, ?U_SLit, Hn, Hp, !Z.add_0_r.
rewrite !unsigned_lit_small by lia.
cbn [zalu_raw zmd_raw Z.of_N].
change (zcanon 32) with 32. change (zcanon 446676598784) with 446676598784.
change (Z.land 32 63) with 32.
rewrite (zcanon_id i), (zcanon_id b) by (unfold M64; lia).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
rewrite (zcanon_id (i * 4294967296)) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia.
replace (i * 4294967296 * 446676598784) with (104 * i * 2 ^ 64)
  by (change (2 ^ 64) with 18446744073709551616; lia).
rewrite Z.div_mul by (change (2 ^ 64) with 18446744073709551616; lia).
rewrite (zcanon_id (104 * i)) by (unfold M64; lia).
apply zcanon_id. unfold M64. lia.
Qed.

Lemma m2k_U_a0 : forall E (n p : nat) (i b : Z),
  ew E n = Z_to_bv 64 i -> 0 <= i <= 32 ->
  ew E p = Z_to_bv 64 b -> 0 <= b -> b + 104 * i < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff p 0)
        (SMd M_MULHU (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 446676598784)))
  = b + 104 * i.
Proof.
intros E n p i b Hn Hi Hp Hb Hs. unfold U.
rewrite (m2k_denot_a0 E n p i b Hn Hi Hp Hb Hs).
apply unsigned_lit_small. lia.
Qed.

Definition m2k_sx (v : Z) : Z := if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32).

Lemma m2k_U_sext32 : forall E (n : nat) (v : Z),
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt true 32 (SOff n 0)) = m2k_sx v.
Proof.
intros E n v H Hv.
rewrite U_SExt, (U_atom E n v H ltac:(lia)).
cbn [Z.of_N].
rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold m2k_sx, zcanon, M64, bv_swrap, bv_wrap.
change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
destruct (Z.ltb_spec v (2 ^ 31)) as [Hl|Hl]; cbv beta iota.
- rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia.
  rewrite Z.mod_small by lia. lia.
- replace ((v + 2 ^ 31) mod 2 ^ 32) with (v + 2 ^ 31 - 2 ^ 32)
    by (apply (Z.mod_unique _ _ 1); lia).
  symmetry. apply (Z.mod_unique _ _ (-1)); lia.
Qed.

Lemma m2k_sx_eq : forall v w, 0 <= v < 2 ^ 32 -> 0 <= w < 2 ^ 31 -> (m2k_sx v = w <-> v = w).
Proof.
intros v w Hv Hw. unfold m2k_sx.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; split; intros; lia.
Qed.

Lemma m2k_sx_range : forall v, 0 <= v < 2 ^ 32 -> 0 <= m2k_sx v < 2 ^ 64.
Proof.
intros v Hv. unfold m2k_sx.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; lia.
Qed.

Lemma m2k_sx_id : forall v, 0 <= v < 2 ^ 31 -> m2k_sx v = v.
Proof.
intros v Hv. unfold m2k_sx.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; lia.
Qed.

Lemma m2k_denot_of_U : forall E (a : sv) (v : Z), U E a = v -> sv_denot E a = Z_to_bv 64 v.
Proof.
intros E a v H. rewrite (denot_lit_U E a), H. reflexivity.
Qed.

(* the int32 value of a 32-bit pattern has the pattern as its low 32 bits *)
Lemma m2k_s32_mod : forall z, 0 <= z < 2 ^ 32 -> Accessors.s32 z mod 2 ^ 32 = z.
Proof.
intros z Hz. unfold Accessors.s32.
destruct (Z.ltb_spec z (2 ^ 31)); cbv beta iota.
- apply Z.mod_small. lia.
- symmetry. apply (Z.mod_unique _ _ (-1)); lia.
Qed.

(* a register's value as the denotation of its symbolic value, without unfolding sv_denot *)
Ltac m2k_rsv HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Hr : getr (ms_regs ms) r = sv_denot E e)
by (refine (eq_trans (st_ok_restrict_reg segs H E ss ms r HS) (f_equal (sv_denot E) _)); vm_compute; reflexivity)
end.

(* ===================================== the model facts ===================================== *)
(* What a key entry is, the text of a NUL-terminated body, the pairs of the scan across the key, what the value
   entry's type and size decide, and the record's bounds (lib/Pod's Rate / Accessors / Layout). *)
Definition m2k_d : ent := Ent 0 0 [].

Lemma m2k_skipn_cons : forall {A : Type} (l : list A) (j : nat) (d : A), (j < length l)%nat ->
skipn j l = nth j l d :: skipn (S j) l.
Proof.
intros A l. induction l as [|x l IH]; intros j d Hj; cbn [length] in Hj; [lia|].
destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in Hj. lia.
Qed.

Lemma m2k_pairs_skip : forall (es : list ent) (m : nat), (m < length es)%nat ->
key_of (nth m es m2k_d) = None ->
pairs_by key_of (skipn m es) None = pairs_by key_of (skipn (S m) es) None.
Proof.
intros es m Hm Hk. rewrite (m2k_skipn_cons es m m2k_d Hm). cbn [pairs_by]. rewrite Hk. reflexivity.
Qed.

Lemma m2k_pairs_run : forall (es : list ent) (a m : nat), (a <= m)%nat -> (m <= length es)%nat ->
(forall q, (a <= q < m)%nat -> key_of (nth q es m2k_d) = None) ->
pairs_by key_of (skipn a es) None = pairs_by key_of (skipn m es) None.
Proof.
intros es a m. remember (m - a)%nat as n eqn:Hn. revert a m Hn.
induction n as [|n IH]; intros a m Hn Ham Hml Hq.
- assert (a = m) as -> by lia. reflexivity.
- rewrite (m2k_pairs_skip es a ltac:(lia) (Hq a ltac:(lia))).
  apply (IH (S a) m); [lia | lia | lia |]. intros q Hqq. apply Hq. lia.
Qed.

Lemma m2k_pairs_key : forall (es : list ent) (m : nat) (kb : list byte), (S m < length es)%nat ->
key_of (nth m es m2k_d) = Some kb ->
pairs_by key_of (skipn m es) None = (kb, nth (S m) es m2k_d) :: pairs_by key_of (skipn (S (S m)) es) None.
Proof.
intros es m kb Hm Hk.
rewrite (m2k_skipn_cons es m m2k_d ltac:(lia)). cbn [pairs_by]. rewrite Hk.
rewrite (m2k_skipn_cons es (S m) m2k_d Hm). cbn [pairs_by]. reflexivity.
Qed.

(* the scan's invariant at the key m: the pairs are (kb, ent[m + 1]), then the pairs from m + 2 on *)
Lemma m2k_inv_key : forall (rec : pod_rec) (a m : nat) (kb : list byte), rs_scan_inv rec a ->
(a <= m)%nat -> (S m < length (ents rec))%nat ->
(forall q, (a <= q < m)%nat -> key_of (nth q (ents rec) m2k_d) = None) ->
key_of (nth m (ents rec) m2k_d) = Some kb ->
rs_E0 rec = Rate.rate_of_pairs Rate.expect_value
 ((kb, nth (S m) (ents rec) m2k_d) :: pairs_by key_of (skipn (S (S m)) (ents rec)) None).
Proof.
intros rec a m kb (Hle & He) Ham Hm Hq Hk.
rewrite He, (m2k_pairs_run (ents rec) a m Ham ltac:(lia) Hq), (m2k_pairs_key (ents rec) m kb Hm Hk).
reflexivity.
Qed.

Lemma m2k_rop_cons : forall vf k e ps,
  Rate.rate_of_pairs vf ((k, e) :: ps) =
  (if Cursor.bytes_eqb k Rate.RATE_KEY then vf e else Rate.rate_of_pairs vf ps).
Proof.
intros vf k e ps. unfold Rate.rate_of_pairs. cbn [find fst].
destruct (Cursor.bytes_eqb k Rate.RATE_KEY); reflexivity.
Qed.

Lemma m2k_bytes_eqb_false : forall a b, a <> b -> Cursor.bytes_eqb a b = false.
Proof.
intros a b H. destruct (Cursor.bytes_eqb a b) eqn:E; [|reflexivity].
apply Cursor.bytes_eqb_eq in E. contradiction.
Qed.

(* (b) the key is not "reac.cfg.rate": the invariant moves to m + 2, where the scan's outer head goes on *)
Lemma m2k_inv_mismatch : forall (rec : pod_rec) (at0 m : nat) (kb : list byte),
  rs_scan_inv rec at0 -> (at0 <= m)%nat -> (S m < length (ents rec))%nat ->
  (forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) m2k_d) = None) ->
  key_of (nth m (ents rec) m2k_d) = Some kb -> kb <> Rate.RATE_KEY ->
  rs_scan_inv rec (S (S m)).
Proof.
intros rec at0 m kb Hinv Ham Hm Hq Hk Hne.
pose proof (m2k_inv_key rec at0 m kb Hinv Ham Hm Hq Hk) as E.
split; [lia|].
rewrite E, m2k_rop_cons, (m2k_bytes_eqb_false kb Rate.RATE_KEY Hne). reflexivity.
Qed.

(* (a) the key is "reac.cfg.rate": the answer is the value entry's *)
Lemma m2k_inv_match : forall (rec : pod_rec) (at0 m : nat) (kb : list byte),
  rs_scan_inv rec at0 -> (at0 <= m)%nat -> (S m < length (ents rec))%nat ->
  (forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) m2k_d) = None) ->
  key_of (nth m (ents rec) m2k_d) = Some kb -> kb = Rate.RATE_KEY ->
  rs_E0 rec = Rate.expect_value (nth (S m) (ents rec) m2k_d).
Proof.
intros rec at0 m kb Hinv Ham Hm Hq Hk Heq. subst kb.
rewrite (m2k_inv_key rec at0 m Rate.RATE_KEY Hinv Ham Hm Hq Hk), m2k_rop_cons.
assert (Cursor.bytes_eqb Rate.RATE_KEY Rate.RATE_KEY = true) as -> by (apply Cursor.bytes_eqb_eq; reflexivity).
reflexivity.
Qed.

(* the value entry's type and size decide Rate.expect_value *)
Lemma m2k_expect_int : forall e, e_type e = POD_INT -> 4 <= e_size e ->
  Rate.expect_value e = (Some (Accessors.s32 (Cursor.rd32 (e_body e))), 1).
Proof.
intros e Ht Hs. unfold Rate.expect_value, Accessors.int_of. rewrite Ht.
rewrite (proj2 (Z.leb_le 4 (e_size e)) Hs).
assert (E : (POD_INT =? POD_INT) = true) by reflexivity. rewrite E. cbn [andb]. reflexivity.
Qed.

Lemma m2k_expect_float : forall e, e_type e = POD_FLOAT -> 4 <= e_size e ->
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

Lemma m2k_expect_none : forall e,
  (e_type e <> POD_INT /\ e_type e <> POD_FLOAT) \/ e_size e < 4 ->
  Rate.expect_value e = (None, -1).
Proof.
intros e [[H1 H2]|H3]; unfold Rate.expect_value, Accessors.int_of, Accessors.float_of.
- rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
- rewrite (proj2 (Z.leb_gt 4 (e_size e)) H3).
  rewrite !andb_false_r. reflexivity.
Qed.

(* what a key entry is, and the text a NUL-terminated body holds *)
Lemma m2k_key_of_some : forall (e : ent) (kb : list byte), key_of e = Some kb ->
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

Lemma m2k_cstr_bytes : forall (l : list byte) (k : nat), (k < length l)%nat ->
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

Lemma m2k_map_bv_inj : forall (a b : list byte),
  map (fun x : byte => bv_unsigned x) a = map (fun x : byte => bv_unsigned x) b -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn [map] in H; try discriminate H; [reflexivity|].
injection H as Hxy Hab. f_equal; [apply bv_eq; exact Hxy | apply IH; exact Hab].
Qed.

(* the record's bounds *)
Lemma m2k_nent_le : forall (rec : pod_rec), pod_rec_wf rec -> (length (ents rec) <= 32)%nat.
Proof. intros rec H. exact (proj1 (ents_wf rec H)). Qed.

Lemma m2k_ent_wf_nth : forall (rec : pod_rec) (m : nat), pod_rec_wf rec -> (m < length (ents rec))%nat ->
ent_wf (nth m (ents rec) m2k_d).
Proof.
intros rec m Hw Hm. pose proof (proj2 (ents_wf rec Hw)) as HF.
rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hm.
Qed.

Lemma m2k_buf_max : forall rec, pod_rec_wf rec -> Z.of_nat (length (Model.buf rec)) <= Layout.POD_BUF_MAX.
Proof.
intros rec (Hs & Hk & He & Hl & HL & Hc). unfold Model.buf, Layout.POD_BUF_MAX.
destruct (p_corr rec) as [[off bs]|].
- destruct Hc as (Ho & Hb & _). unfold Model.overwrite. rewrite !length_app, length_firstn, length_skipn. lia.
- lia.
Qed.

Lemma m2k_bodies_96 : forall rec, pod_rec_wf rec ->
  Forall (fun e => (length (Model.e_body e) <= 96)%nat) (ents rec).
Proof.
intros rec Hw. pose proof (proj2 (ents_wf rec Hw)) as HF.
eapply Forall_impl; [|exact HF]. intros e (_ & Hb & Hs). cbv beta. lia.
Qed.

(* the entry's 104-byte image: its type, its size, and the 4 bytes at offset 8 (the body word m2k_bw, which is
   rd32 of the body when the size is at least 4) *)
Definition m2k_bw (e : ent) : Z := bytes_le_to_Z (rtm_slice (Layout.ent_mem e) 8 4).

Lemma m2k_ent_mem_len : forall e, ent_wf e -> length (Layout.ent_mem e) = 104%nat.
Proof. intros e (_ & Hb & Hs). apply Layout.length_ent_mem. lia. Qed.

Lemma m2k_ent_type_slice : forall e, rtm_slice (Layout.ent_mem e) 0 4 = Z_to_le_bytes 4 (e_type e).
Proof.
intros e. unfold rtm_slice, Layout.ent_mem. cbn [skipn].
change (Z_to_le_bytes 4 (e_type e)) with (Cursor.le32 (e_type e)).
apply Layout.firstn_app_eq. reflexivity.
Qed.

Lemma m2k_ent_size_slice : forall e, rtm_slice (Layout.ent_mem e) 4 4 = Z_to_le_bytes 4 (e_size e).
Proof.
intros e. unfold rtm_slice, Layout.ent_mem.
rewrite (Layout.skipn_app_eq (Cursor.le32 (e_type e))) by reflexivity.
change (Z_to_le_bytes 4 (e_size e)) with (Cursor.le32 (e_size e)).
apply Layout.firstn_app_eq. reflexivity.
Qed.

Lemma m2k_ent_bw_slice : forall e, ent_wf e -> rtm_slice (Layout.ent_mem e) 8 4 = Z_to_le_bytes 4 (m2k_bw e).
Proof.
intros e He. unfold m2k_bw.
assert (Hl : length (rtm_slice (Layout.ent_mem e) 8 4) = 4%nat).
{ unfold rtm_slice. rewrite length_firstn, length_skipn, (m2k_ent_mem_len e He). reflexivity. }
pose proof (YA0d.Z_to_le_bytes_to_Z (rtm_slice (Layout.ent_mem e) 8 4)) as HZ. rewrite Hl in HZ.
symmetry. exact HZ.
Qed.

Lemma m2k_bw_range : forall e, ent_wf e -> 0 <= m2k_bw e < 2 ^ 32.
Proof.
intros e He. unfold m2k_bw.
assert (Hl : length (rtm_slice (Layout.ent_mem e) 8 4) = 4%nat).
{ unfold rtm_slice. rewrite length_firstn, length_skipn, (m2k_ent_mem_len e He). reflexivity. }
pose proof (rtm_lez_range (rtm_slice (Layout.ent_mem e) 8 4)) as H. rewrite Hl in H. exact H.
Qed.

Lemma m2k_bw_rd32 : forall e, ent_wf e -> 4 <= e_size e -> m2k_bw e = Cursor.rd32 (e_body e).
Proof.
intros e (_ & Hb & Hs) H4. unfold m2k_bw, Cursor.rd32, rtm_slice, Layout.ent_mem.
assert (E : forall (a b : Z) (X : list byte), skipn 8 (Cursor.le32 a ++ Cursor.le32 b ++ X) = X)
  by (intros; reflexivity).
rewrite E, firstn_app.
replace (4 - length (e_body e))%nat with 0%nat by lia.
cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

(* ===================================== the engine's facts, regions and shadow ===================================== *)
(* atom 9 is s1 = R, atom 18 is s2 = the runtime's shadow offset, atom 10 is a0 = &ent[v] *)
Definition m2k_facts10 : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
          (10%nat, mkAF 4096 0x7fffff800000 0) ] [] [].
(* the five checks of this half read shadow bytes of [&ent[v], &ent[v] + 16) *)
Definition m2k_SH : list shent := [ mkSHE 10 0 16 ].
(* the value entry: its type, its size and its body word *)
Definition m2k_ent (t s bw : sv) : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 0
  [YP09.mkChunk 0 (CVal 4 t); YP09.mkChunk 4 (CVal 4 s); YP09.mkChunk 8 (CVal 4 bw)].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma m2k_facts10_ok : forall E R a,
bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 18) = SHADOW_OFF ->
bv_unsigned (ew E 10) = a -> 4096 <= a <= 0x7fffff800000 -> facts_ok E m2k_facts10.
Proof.
intros E R a H9 HR Hal H18 H10 Ha. split; [|split; [exact I | exact I]].
cbn [m2k_facts10 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H9, H18, H10. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; try lia.
all: try apply Z.mod_1_r.
Qed.

(* the shadow entry: every byte of [a, a + 16) is marked usable and the range is apart from the shadow band *)
Lemma m2k_sh_ok : forall (W : world rsegs) mem E a,
U E M2_Bx = SHADOW_OFF -> U E (SOff 10 0) = a ->
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a 16 ->
(a + 16 <= kLowShadowBeg \/ kHighMemBeg <= a) ->
sh_ok rsegs M2_Bx m2k_SH E (mrestrict (w_H W) mem).
Proof.
intros W mem E a HB H10 Hra Happ. apply Forall_cons; [|apply Forall_nil].
apply (YCbq.shent_ok_of_range rsegs (w_H W) mem E M2_Bx 10 a 16 a 0 16 Hra HB H10 ltac:(lia) ltac:(lia)).
intros x Hx. cbn [Z.min Z.max] in Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
End b.

(* ===================================== the interfaces of the pieces ===================================== *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the value entry e at a0v in a state's view: its type, size and body word, its 16 bytes marked usable, inside the
   allocator's range and apart from the shadow band *)
Definition m2k_ent_facts (W : world rsegs) (mem : word -> option byte) (e : ent) (a0v : Z) : Prop :=
ent_wf e /\
val_mem rsegs (mrestrict (w_H W) mem) a0v 4 (e_type e) /\
val_mem rsegs (mrestrict (w_H W) mem) (a0v + 4) 4 (e_size e) /\
val_mem rsegs (mrestrict (w_H W) mem) (a0v + 8) 4 (m2k_bw e) /\
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a0v 16 /\
4096 <= a0v /\ a0v + 16 <= alloc_ceiling /\ (a0v + 16 <= kLowShadowBeg \/ kHighMemBeg <= a0v).

(* the model side of the match: the answer is the value entry's, and the parse's answer is the scan's *)
Definition m2k_match (cx : rs_scx rsegs) (rec : pod_rec) (e : ent) : Prop :=
rs_E0 rec = Rate.expect_value e /\ snd (rs_PA rsegs cx rec) = snd (rs_E0 rec) /\
fst (rs_PA rsegs cx rec) = fst (rs_E0 rec).

(* KV 0x82b14: the key matched and a0 = &ent[v] *)
Definition m2k_K_val (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec) : Prop :=
forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3 (e : ent) (a0v : Z),
rs_chk_base (fx := fx) rsegs B MT cx fx3 rec rs_PZ ly3 S3 W3 regs3 mem3 md3 ->
rs_hz_at rsegs cx rec W3 mem3 ->
rs_at_cx rsegs cx W3 mem3 regs3
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 10, a0v);
                        (LCell XR 0x78, q_F (x_e rsegs cx)); (LCell XR 0xc0, q_pp (x_e rsegs cx))]) ->
m2k_ent_facts W3 mem3 e a0v -> m2k_match cx rec e ->
SRr rsegs W3 (@cfg_at fx3 rsegs M2K_KV regs3 mem3 md3) POST.

(* FLT 0x82c44: s6 = F and s10 = the flags byte are loaded (the facts of A's cut hold), a0 = &ent[v], type 6 *)
Definition m2k_K_float (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec) : Prop :=
forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3 (e : ent) (a0v : Z),
rs_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 10) = w64 a0v ->
m2k_ent_facts W3 mem3 e a0v -> e_type e = POD_FLOAT -> m2k_match cx rec e ->
SRr rsegs W3 (@cfg_at fx3 rsegs M2K_FLT regs3 mem3 md3) POST.

(* JN 0x82c8c: the facts of A's cut hold, the answer is a rate, and a2 holds the value as a sign-extended
   32-bit word (the value the hz cell holds) *)
Definition m2k_K_join (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec) : Prop :=
forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3,
rs_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ->
snd (rs_PA rsegs cx rec) = 1 ->
getr regs3 (Z_to_bv 5 12) = w64 (m2k_sx (rs_hz rsegs cx rec mod 2 ^ 32)) ->
SRr rsegs W3 (@cfg_at fx3 rsegs M2K_JN regs3 mem3 md3) POST.

(* the four pieces, each one stretch of code between the pcs above; rt_m02_key_A chains them *)
(* JN 0x82c8c -> A: a1 := the hz cell, a0 := s8, check_rate, j A *)
Definition m2k_join_stmt : Prop :=
forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec),
rs_pre rsegs B cx -> rs_from_A (fx := fx) rsegs B MT cx POST -> m2k_K_join cx POST rec.
(* FLT 0x82c44 -> MAL / JN: the size, the flw, pod_nearest, the out cell *)
Definition m2k_float_stmt : Prop :=
forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec),
rs_pre rsegs B cx -> rs_from_MAL (fx := fx) rsegs B MT cx POST -> m2k_K_join cx POST rec ->
m2k_K_float cx POST rec.
(* KV 0x82b14 -> FLT / MAL / JN: the type, s6 / s10, the Int arm *)
Definition m2k_val_stmt : Prop :=
forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec),
rs_pre rsegs B cx -> rs_from_MAL (fx := fx) rsegs B MT cx POST -> m2k_K_float cx POST rec ->
m2k_K_join cx POST rec -> m2k_K_val cx POST rec.
(* KM 0x82aac -> O / KV: the dead `blt`, the spills, the strcmp wrapper, the reloads, the mismatch exit, &ent[v] *)
Definition m2k_key_stmt : Prop :=
forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (inp : list byte) (at0 m : nat),
rs_start_M02 (fx := fx) rsegs B cx inp -> rs_from_O (fx := fx) rsegs B MT cx POST (S (S m)) ->
(forall rec, m2k_K_val cx POST rec) -> rs_from_KM (fx := fx) rsegs B MT cx POST at0 m.
End i.

(* the registers rs_L_chk names: s0, s1, s2, s4, s5, all callee-saved; m2k_get reads one through a cs_eq *)
Definition m2k_L5 : list (bv 5) := [8; 9; 18; 20; 21]%bv.
Lemma m2k_L5_cs : forall r, In r m2k_L5 -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [m2k_L5 In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
Ltac m2k_get Hcs r :=
etransitivity; [exact (Hcs r ltac:(cbv [m2k_L5 ch_L In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].

(* ===================================== the cut facts across a call or a run ===================================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the first block and the frame for locals lie below the allocator's ceiling, which lies below the callees'
   stack; the first block lies apart from the shadow band *)
Lemma m2k_apart : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
4096 <= q_pp (x_e rsegs cx) /\ q_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling /\
(q_pp (x_e rsegs cx) + Layout.PP_SIZE <= kLowShadowBeg \/ kHighMemBeg <= q_pp (x_e rsegs cx)) /\
4096 <= q_F (x_e rsegs cx) /\ q_F (x_e rsegs cx) + 512 <= alloc_ceiling /\
alloc_ceiling <= q_R (x_e rsegs cx) - T_SEG_STK /\ 2 ^ 46 <= q_R (x_e rsegs cx) <= 2 ^ 47.
Proof.
intros cx Hpre. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2_stack B cx Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
pose proof (m2_frameF B cx Hpre) as (_ & HF0 & HFc & _ & _).
pose proof Hpre as Hpre'. unfold rs_pre, rt_seg_pre in Hpre'.
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

(* the bytes this half (its runs and its three callees) may change: the callees' stack below R, the four spill
   cells R+0x110, R+0x118, R+0x128, R+0x130 and pod_nearest's out cell R+0x158 *)
Definition m2k_wz (cx : rs_scx rsegs) (a : Z) : Prop :=
(q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) \/
(q_R (x_e rsegs cx) + 0x110 <= a < q_R (x_e rsegs cx) + 0x120) \/
(q_R (x_e rsegs cx) + 0x128 <= a < q_R (x_e rsegs cx) + 0x138) \/
(q_R (x_e rsegs cx) + 0x158 <= a < q_R (x_e rsegs cx) + 0x160).

(* a byte below the allocator's ceiling is outside that zone *)
Lemma m2k_far_low : forall cx : rs_scx rsegs, rs_pre rsegs B cx -> forall a, 0 <= a < alloc_ceiling ->
0 <= a < 2 ^ 64 /\ ~ m2k_wz cx a.
Proof.
intros cx Hpre a Ha. pose proof (m2k_apart cx Hpre) as (_ & _ & _ & _ & _ & Hc & H46).
pose proof asan_consts as (C1 & _). unfold m2k_wz, T_SEG_STK, ASTACK in *. lia.
Qed.

(* a real-frame cell [R + o, R + o + 8) apart from the spill run and the out cell is outside that zone *)
Lemma m2k_far_cell : forall cx : rs_scx rsegs, rs_pre rsegs B cx -> forall o k,
0 <= o -> o + 8 <= 0x1e0 -> 0 <= k < 8 ->
(o + 8 <= 0x110 \/ (0x120 <= o /\ o + 8 <= 0x128) \/ (0x138 <= o /\ o + 8 <= 0x158) \/ 0x160 <= o) ->
0 <= q_R (x_e rsegs cx) + o + k < 2 ^ 64 /\ ~ m2k_wz cx (q_R (x_e rsegs cx) + o + k).
Proof.
intros cx Hpre o k Ho Ho8 Hk Hz. pose proof (m2k_apart cx Hpre) as (_ & _ & _ & _ & _ & Hc & H46).
unfold m2k_wz, T_SEG_STK, ASTACK in *. lia.
Qed.

(* rs_chk_base and the hz cell, carried to a state whose memory agrees outside m2k_wz, at a float state that
   keeps every float register outside fa0, fa3, fa4, fa5 *)
Lemma m2k_base_kept : forall (cx : rs_scx rsegs) (fx2 fx3 : YK11.FPState) rec
ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx -> rs_chk_base (fx := fx) rsegs B MT cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 ->
rs_hz_at rsegs cx rec W2 mem2 ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> rt_fxk [10; 13; 14; 15] fx fx3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ m2k_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_chk_base (fx := fx) rsegs B MT cx fx3 rec rs_PZ ly3 S3 W3 regs3 mem3 md3 /\ rs_hz_at rsegs cx rec W3 mem3.
Proof.
intros cx fx2 fx3 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre
(Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1) Hhz Hcore3 Hfxk3 K3.
pose proof (m2_frameF B cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof (m2_pp B cx Hpre) as (P4096 & Pceil & _).
pose proof (m2k_far_low cx Hpre) as Far.
pose proof ck_segs_low as Hsegs. pose proof asan_consts as (C1 & _).
split.
- split; [exact Hcore3|]. split; [exact Hfxk3|].
  split.
  { apply (rtm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ Hfsh). intros i Hi.
    assert (Hlen56 : Z.of_nat (length rs_PZ) = 56) by (vm_compute; reflexivity). rewrite Hlen56 in Hi.
    assert (Hsh : 0 <= shadow_addr (q_F (x_e rsegs cx)) + i < alloc_ceiling).
    { unfold shadow_addr, SHADOW_OFF.
      pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (q_F (x_e rsegs cx)) 8 ltac:(lia)) as M.
      assert (0 <= q_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
      lia. }
    destruct (Far _ Hsh) as (Hb & Hs). apply K3; assumption. }
  split.
  { eapply (rtm_rom_kept rsegs); [exact Hrom|]. intros a (sg & Hsg & _ & Hr).
    pose proof (Hsegs a ltac:(exists sg; split; [exact Hsg | exact Hr])) as Hl. unfold kLowMemEnd in Hl.
    destruct (Far a ltac:(lia)) as (Hb & Hs). apply K3; assumption. }
  split.
  { unfold rs_pp_at in *. apply (ch_garr8_kept _ _ _ _ _ _ Hpp). intros j Hj.
    unfold rs_u8s in Hj. rewrite length_map in Hj. pose proof (Layout.length_pp_bytes rec Hwf) as HL0.
    destruct (Far (q_pp (x_e rsegs cx) + Z.of_nat j) ltac:(lia)) as (Hb & Hs). apply K3; assumption. }
  split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hpod0|]. split; [exact Hpod | exact Hpod1].
- unfold rs_hz_at in *. eapply (val_mem_kept rsegs); [|exact Hhz]. intros k Hk. change (Z.of_nat 4) with 4 in Hk.
  destruct (Far (q_F (x_e rsegs cx) + 0x180 + k) ltac:(lia)) as (Hb & Hs). apply K3; assumption.
Qed.

(* a real-frame cell apart from the spill run and the out cell, carried the same way *)
Lemma m2k_cell_kept : forall (cx : rs_scx rsegs) (W2 : world rsegs) mem2 (W3 : world rsegs) mem3 o v,
rs_pre rsegs B cx -> 0 <= o -> o + 8 <= 0x1e0 ->
(o + 8 <= 0x110 \/ (0x120 <= o /\ o + 8 <= 0x128) \/ (0x138 <= o /\ o + 8 <= 0x158) \/ 0x160 <= o) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ m2k_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + o) 8 v ->
val_mem rsegs (mrestrict (w_H W3) mem3) (q_R (x_e rsegs cx) + o) 8 v.
Proof.
intros cx W2 mem2 W3 mem3 o v Hpre Ho Ho8 Hz K3 Hv.
eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
destruct (m2k_far_cell cx Hpre o k Ho Ho8 Hk Hz) as (Hb & Hs). apply K3; assumption.
Qed.

(* rs_L_chk's facts, carried to a state whose registers s0, s1, s2, s4, s5 (m2k_L5) agree and whose memory agrees
   outside m2k_wz *)
Lemma m2k_chk_kept : forall (cx : rs_scx rsegs) W2 mem2 regs2 W3 mem3 regs3,
rs_pre rsegs B cx ->
rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_chk rsegs cx) -> cs_eq m2k_L5 regs2 regs3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ m2k_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_at_cx rsegs cx W3 mem3 regs3 (rs_L_chk rsegs cx).
Proof.
intros cx W2 mem2 regs2 W3 mem3 regs3 Hpre Hat HL K3.
unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc in Hat. rewrite Forall_app, !Forall_cons_iff in Hat.
destruct Hat as ((A8 & A9 & A20 & A18 & AC138 & A21 & AC18 & AC58 & _) &
                 (AC20 & AC38 & AC40 & AC48 & AC50 & AC120 & _)).
cbn [rt_at rt_xv fst snd] in A8, A9, A20, A18, AC138, A21, AC18, AC58, AC20, AC38, AC40, AC48, AC50, AC120.
unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc. cbn [app].
repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
- m2k_get HL (8%bv : bv 5). exact A8.
- m2k_get HL (9%bv : bv 5). exact A9.
- m2k_get HL (20%bv : bv 5). exact A20.
- m2k_get HL (18%bv : bv 5). exact A18.
- apply (m2k_cell_kept cx W2 mem2 W3 mem3 0x138); [exact Hpre | lia | lia | lia | exact K3 | exact AC138].
- m2k_get HL (21%bv : bv 5). exact A21.
- apply (m2k_cell_kept cx W2 mem2 W3 mem3 0x18); [exact Hpre | lia | lia | lia | exact K3 | exact AC18].
- apply (m2k_cell_kept cx W2 mem2 W3 mem3 0x58); [exact Hpre | lia | lia | lia | exact K3 | exact AC58].
- apply (m2k_cell_kept cx W2 mem2 W3 mem3 0x20); [exact Hpre | lia | lia | lia | exact K3 | exact AC20].
- apply (m2k_cell_kept cx W2 mem2 W3 mem3 0x38); [exact Hpre | lia | lia | lia | exact K3 | exact AC38].
- apply (m2k_cell_kept cx W2 mem2 W3 mem3 0x40); [exact Hpre | lia | lia | lia | exact K3 | exact AC40].
- apply (m2k_cell_kept cx W2 mem2 W3 mem3 0x48); [exact Hpre | lia | lia | lia | exact K3 | exact AC48].
- apply (m2k_cell_kept cx W2 mem2 W3 mem3 0x50); [exact Hpre | lia | lia | lia | exact K3 | exact AC50].
- apply (m2k_cell_kept cx W2 mem2 W3 mem3 0x120); [exact Hpre | lia | lia | lia | exact K3 | exact AC120].
Qed.

(* A's cut at a later state: from the facts of A's cut (or of any cut of the half that carries them), the
   registers s0, s1, s2, s4, s5, s8, s6, s10 as there, the memory as there outside m2k_wz, and the float state kept
   outside fa0, fa3, fa4, fa5 *)
Lemma m2k_cut_A : forall (cx : rs_scx rsegs) (fx2 fx3 : YK11.FPState) rec
ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx -> rs_chk_base (fx := fx) rsegs B MT cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 ->
rs_hz_at rsegs cx rec W2 mem2 ->
rs_at_cx rsegs cx W2 mem2 regs2
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec));
                        (LCell XR 0x78, q_F (x_e rsegs cx)); (LCell XR 0xc0, q_pp (x_e rsegs cx))]) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> rt_fxk [10; 13; 14; 15] fx fx3 ->
cs_eq m2k_L5 regs2 regs3 -> getr regs3 (Z_to_bv 5 24) = getr regs2 (Z_to_bv 5 24) ->
getr regs3 (Z_to_bv 5 22) = w64 (q_F (x_e rsegs cx)) ->
getr regs3 (Z_to_bv 5 26) = w64 (q_fl (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ m2k_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx fx2 fx3 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hhz Hat Hcore3 Hfxk3
HL H24 H22 H26 K3.
destruct (m2k_base_kept cx fx2 fx3 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hhz Hcore3
  Hfxk3 K3) as (Hbase3 & Hhz3).
assert (HatL : rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_chk rsegs cx)).
{ unfold rs_at_cx, rs_at in Hat |- *. rewrite Forall_app in Hat. exact (proj1 Hat). }
pose proof (m2k_chk_kept cx W2 mem2 regs2 W3 mem3 regs3 Hpre HatL HL K3) as HatL3.
unfold rs_at_cx, rs_at in Hat. rewrite Forall_app, !Forall_cons_iff in Hat.
destruct Hat as (_ & A24 & AC78 & ACc0 & _). cbn [rt_at rt_xv fst snd] in A24, AC78, ACc0.
split; [exact Hbase3|]. split; [|exact Hhz3].
unfold rs_at_cx, rs_at in HatL3 |- *. rewrite Forall_app. split; [exact HatL3|].
repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
- rewrite H24. exact A24.
- exact H22.
- exact H26.
- apply (m2k_cell_kept cx W2 mem2 W3 mem3 0x78); [exact Hpre | lia | lia | lia | exact K3 | exact AC78].
- apply (m2k_cell_kept cx W2 mem2 W3 mem3 0xc0); [exact Hpre | lia | lia | lia | exact K3 | exact ACc0].
Qed.

(* MAL's cut is A's when the answer is (None, -1) *)
Lemma m2k_mal_of_A : forall (cx : rs_scx rsegs) (fx3 : YK11.FPState) rec ly3 S3 W3 regs3 mem3 md3,
rs_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ->
fst (rs_PA rsegs cx rec) = None -> snd (rs_PA rsegs cx rec) = -1 ->
rs_cut_MAL (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (Hb & Ha & Hh) Hn Hm.
rewrite Hm in Ha. split; [exact Hb|]. split; [exact Ha|]. split; [exact Hh|]. split; [exact Hn | exact Hm].
Qed.

(* the value entry ent[v] at a state of the half: its facts at &ent[v] = pp + 0x4014 + 104 v *)
Lemma m2k_ent_at : forall (cx : rs_scx rsegs) (fx2 : YK11.FPState) rec ly2 S2 W2 regs2 mem2 md2 (v : nat),
rs_pre rsegs B cx -> rs_chk_base (fx := fx) rsegs B MT cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 ->
(v < length (ents rec))%nat ->
m2k_ent_facts W2 mem2 (nth v (ents rec) m2k_d) (q_pp (x_e rsegs cx) + 0x4014 + 104 * Z.of_nat v).
Proof.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 v Hpre
(Hcore & _ & _ & _ & Hpp & Hwf & _) Hv.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2k_apart cx Hpre) as (Hp0 & Hpc & Happ & _).
pose proof (m2k_nent_le rec Hwf) as Hn32.
pose proof (m2k_ent_wf_nth rec v Hwf Hv) as Hewf.
set (e := nth v (ents rec) m2k_d).
set (a := q_pp (x_e rsegs cx) + 0x4014 + 104 * Z.of_nat v).
assert (B0 : rtm_bytes rsegs (w_H W2) mem2 (q_pp (x_e rsegs cx)) (Layout.pp_bytes rec)) by exact Hpp.
unfold Layout.pp_bytes in B0.
pose proof (rtm_pp_ent rsegs (Model.buf rec) (Model.is_props rec) (Model.has_params rec)
  (Model.params_struct rec) (Model.ents rec) (Model.corrupt rec) (m2k_buf_max rec Hwf) Hn32
  (m2k_bodies_96 rec Hwf) (w_H W2) mem2 (q_pp (x_e rsegs cx)) v B0 Hv) as BE.
change (Model.Ent 0 0 []) with m2k_d in BE. fold e in BE.
replace (q_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat v)) with a in BE
  by (unfold a, Layout.OFF_ENT, Layout.ENT_SIZE; lia).
pose proof (m2k_ent_mem_len e Hewf) as HL.
assert (HAR : AR rsegs B ly2 S2 W2 mem2 md2) by exact (proj1 (proj1 Hcore)).
assert (Hin : In (q_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2)).
{ pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
  destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hppin & _).
  destruct Hcore as (_ & _ & _ & Hperm & _).
  apply (Permutation_in _ (Permutation_sym Hperm)). exact Hppin. }
assert (Hreq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
unfold Layout.PP_SIZE in *.
split; [exact Hewf|].
split.
{ replace a with (a + Z.of_nat 0) by lia.
  apply (rtm_bytes_field rsegs (w_H W2) mem2 a (Layout.ent_mem e) 0 4); [exact BE | apply m2k_ent_type_slice | lia]. }
split.
{ replace (a + 4) with (a + Z.of_nat 4) by lia.
  apply (rtm_bytes_field rsegs (w_H W2) mem2 a (Layout.ent_mem e) 4 4); [exact BE | apply m2k_ent_size_slice | lia]. }
split.
{ replace (a + 8) with (a + Z.of_nat 8) by lia.
  apply (rtm_bytes_field rsegs (w_H W2) mem2 a (Layout.ent_mem e) 8 4);
  [exact BE | apply (m2k_ent_bw_slice e Hewf) | lia]. }
split.
{ refine (proj1 (rtm_blk_ra rsegs B ly2 S2 W2 mem2 md2 (q_pp (x_e rsegs cx)) 19744 a 16 HAR Hin _ _));
  unfold a; rewrite ?Hreq; lia. }
unfold a. split; [lia|]. split; [lia|]. destruct Happ as [H|H]; [left | right]; lia.
Qed.
End c.

(* ===================================== helpers of the walks ===================================== *)
(* an extra env slot's denotation *)
Lemma m2k_den_extra : forall regs extra (j : nat) v, nth j extra (Z_to_bv 64 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot (Ereg regs extra) (SOff (32 + j) 0) = Z_to_bv 64 v.
Proof.
intros regs extra j v Hn Hv. apply bv_eq. rewrite denot_SOff, Z.add_0_r, ew_Ereg_extra, Hn.
rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the value entry's facts in a view that agrees everywhere *)
Lemma m2k_ent_facts_kept : forall (W W' : world rsegs) mem mem' e a0v,
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W') mem' a = aview rsegs (w_H W) mem a) ->
m2k_ent_facts W mem e a0v -> m2k_ent_facts W' mem' e a0v.
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
{ apply (rtm_ra_kept rsegs (w_H W) mem (w_H W') mem' SHADOW_OFF a0v 16 Hra). intros x Hx. apply K.
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

(* A's cut after a run of the engine from a state with the KV list's facts: no byte changed, the registers of
   rs_L_chk and s8 kept, s6 = F and s10 = the flags byte *)
Lemma m2k_run_A : forall (cx : rs_scx rsegs) (fx3 : YK11.FPState) rec ly3 S3 W3 regs3 mem3 md3 regsN memN mdN,
rs_pre rsegs B cx ->
rs_chk_base (fx := fx) rsegs B MT cx fx3 rec rs_PZ ly3 S3 W3 regs3 mem3 md3 -> rs_hz_at rsegs cx rec W3 mem3 ->
rs_at_cx rsegs cx W3 mem3 regs3
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec));
                        (LCell XR 0x78, q_F (x_e rsegs cx)); (LCell XR 0xc0, q_pp (x_e rsegs cx))]) ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 memN mdN (x_k rsegs cx) ->
same_io md3 mdN -> cs_eq [2; 3; 4]%bv regs3 regsN -> cs_eq m2k_L5 regs3 regsN ->
getr regsN (Z_to_bv 5 24) = getr regs3 (Z_to_bv 5 24) ->
getr regsN (Z_to_bv 5 22) = w64 (q_F (x_e rsegs cx)) ->
getr regsN (Z_to_bv 5 26) = w64 (q_fl (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W3) memN a = aview rsegs (w_H W3) mem3 a) ->
rs_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 regsN memN mdN.
Proof using MTL.
intros cx fx3 rec ly3 S3 W3 regs3 mem3 md3 regsN memN mdN Hpre Hbase Hhz Hat HJ Hio C234 CL5 H24 H22 H26 K.
pose proof Hbase as (Hcore & Hfxk & _).
assert (HcoreN : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regsN memN mdN).
{ apply (m2_core_step B MT MTL cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 regsN memN mdN Hcore HJ);
  [ intros r Hr; apply C234; cbv [In];
    destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
  | reflexivity | apply Permutation_refl | exact Hio | apply (mo_le_refl MT MTL) |].
  intros a Ha _ _. exact (K a Ha). }
exact (m2k_cut_A B MT cx fx3 fx3 rec ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 regsN memN mdN Hpre Hbase Hhz Hat
  HcoreN Hfxk CL5 H24 H22 H26 (fun a Ha _ => K a Ha)).
Qed.

(* ---- JN 0x82c8c lw a1,0(s5) (the hz cell, z); 0x82c90 mv a0,s8 (= 1); 0x82c94 jal check_rate (ra = 0x82c98),
   a2 already the sign-extended z; then 0x82c98 j A (no region) ---- *)
Lemma m2k_jn_walk : forall (cx : rs_scx rsegs) POST ly2 S2 W2 regs2 mem2 md2 vF vL z,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 21) = w64 (q_F (x_e rsegs cx) + 0x180) -> getr regs2 (Z_to_bv 5 24) = w64 1 ->
getr regs2 (Z_to_bv 5 12) = w64 (m2k_sx z) -> 0 <= z < 2 ^ 32 ->
getr regs2 (Z_to_bv 5 22) = w64 vF -> getr regs2 (Z_to_bv 5 26) = w64 vL ->
val_mem rsegs (mrestrict (w_H W2) mem2) (q_F (x_e rsegs cx) + 0x180) 4 z ->
ch_K B MT cx POST regs2 W2 mem2 vF vL ->
SRr rsegs W2 (cfg_at rsegs M2K_JN regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST ly2 S2 W2 regs2 mem2 md2 vF vL z Hpre Hcore Hsp H21 H24 H12 Hz H22 H26 Hcell HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (E21 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 z]) 21) = q_F (x_e rsegs cx) + 0x180)
by (rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl);
    assert (G : getr regs2 21%bv = w64 (q_F (x_e rsegs cx) + 0x180)) by exact H21;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
assert (D32 : sv_denot (Ereg regs2 [Z_to_bv 64 z]) (SOff 32 0) = Z_to_bv 64 z)
by (apply (m2k_den_extra regs2 _ 0 z); [reflexivity | lia]).
pose proof (m2_entry M2K_JN [] [m2_hzcell (SOff 32 0)] (mkFacts [] [] []) W2 regs2 [Z_to_bv 64 z] mem2
  (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2_hzcell_ok _ W2 mem2 (q_F (x_e rsegs cx)) (SOff 32 0) z E21 ltac:(lia) ltac:(lia) D32 Hz Hcell))
  ltac:(cbn; tauto) ltac:(repeat split)).
remember (Ereg regs2 [Z_to_bv 64 z]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 z]) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
assert (E12 : ew E 12 = Z_to_bv 64 (m2k_sx z))
by (subst E; rewrite (ew_Ereg_nat regs2 _ 12 12%bv eq_refl); exact H12).
assert (E24 : ew E 24 = getr regs2 (Z_to_bv 5 24)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 z) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 M2K_JN) with (Z_to_bv 64 M2K_JN).
(* 0x82c8c .. 0x82c94, stop at check_rate's entry 0x836bc *)
m2_run m2_awr. ck_keep m2_kwr.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
m2k_rsv HS (11%bv : bv 5) G11.
m2k_rsv HS (12%bv : bv 5) G12.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82c98) by exact R1.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [22; 26]%bv HS HAE ltac:(vm_compute; reflexivity)) as C2226;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with A_CHECK_RATE by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs ms) = q_R (x_e rsegs cx))
by (rewrite (m2_sp_of_cs [2; 3; 4]%bv _ _ ltac:(cbv [In]; left; reflexivity) C234); exact Hsp).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdT) _ =>
assert (HcoreT : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore ltac:(eassumption));
    [ intros r Hr; apply C234; cbv [In];
      destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
    | reflexivity | apply Permutation_refl | m2_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KE a Ha (fun x => x)))
end.
eapply SRr_bind.
{ apply (rt_check_rate_A B MT MTL (AR_laws_ok rsegs B) (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
    (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
    ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)).
  - apply (m2_pre_call B MT cx _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ T_check_STK Hpre HcoreT);
    [ rewrite R1'; vm_compute; reflexivity
    | unfold raZ; rewrite R1'; unfold w64; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_check_STK, T_SEG_STK, ASTACK; lia ].
  - etransitivity; [exact R10|]. rewrite E24. exact H24.
  - rewrite G11, G12, !denot_lit_U, (m2k_U_sext32 E 32 z E32 Hz),
      (U_atom E 12 (m2k_sx z) E12 (m2k_sx_range z Hz)).
    reflexivity. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (rs_E2 rsegs cx) (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms)
  (ms_mem ms) _ _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia)
  ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
(* the state at 0x82c98 *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun x => x)).
  exact (KE a Ha (fun x => x)). }
assert (CL3 : cs_eq ch_L regs2 regs3) by exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres ch_L _ _ ch_L_cs Hpres3)).
assert (H223 : getr regs3 (Z_to_bv 5 22) = w64 vF).
{ etransitivity; [exact (Hpres3 22 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact (C2226 22%bv ltac:(cbv [In]; left; reflexivity))|]. exact H22. }
assert (H263 : getr regs3 (Z_to_bv 5 26) = w64 vL).
{ etransitivity; [exact (Hpres3 26 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact (C2226 26%bv ltac:(cbv [In]; right; left; reflexivity))|]. exact H26. }
clear dependent ms. clear dependent E.
pose proof (proj1 Hcore3) as HJ3.
pose proof (m2_entry 0x82c98 [] [] (mkFacts [] [] []) W3 regs3 [] mem3 (Forall_nil _) eq_refl (Forall_nil _)
  ltac:(cbn; tauto) ltac:(repeat split)) as HS.
remember (Ereg regs3 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
by (intros; reflexivity).
change (w64 0x82c98) with (Z_to_bv 64 0x82c98).
m2_run_to m2_awr M2_A. ck_keep m2_kwr.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL';
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [22; 26]%bv HS HAE ltac:(vm_compute; reflexivity)) as C2226';
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with M2_A by (vm_compute; reflexivity)
end.
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
apply (HK ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
end.
- apply (m2_core_step B MT MTL cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 _ _ _ Hcore3 ltac:(eassumption));
  [ intros r Hr; apply C234; cbv [In];
    destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
  | reflexivity | apply Permutation_refl | m2_io | apply (mo_le_refl MT MTL) |].
  intros a Ha _ _. exact (KE a Ha (fun x => x)).
- exact (cs_eq_trans _ _ _ _ CL3 CL').
- etransitivity; [exact (C2226' 22%bv ltac:(cbv [In]; left; reflexivity))|]. exact H223.
- etransitivity; [exact (C2226' 26%bv ltac:(cbv [In]; right; left; reflexivity))|]. exact H263.
- intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (K3 a Ha Hs).
Qed.
End w.

(* ===================================== the pieces ===================================== *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ---- JN -> A ---- *)
Lemma m2k_join : m2k_join_stmt B MT.
Proof using MTL.
unfold m2k_join_stmt, m2k_K_join.
intros cx POST rec Hpre HA fx3 ly3 S3 W3 regs3 mem3 md3 HcA Hrc H12.
pose proof (m2_stack B cx Hpre) as (HR & _).
pose proof HcA as (Hbase & Hat & Hhz).
pose proof Hbase as (Hcore & _).
pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc in Hat'.
rewrite Forall_app, Forall_app, !Forall_cons_iff in Hat'.
destruct Hat' as (((A8 & A9 & A20 & A18 & AC138 & A21 & AC18 & AC58 & _) &
                   (AC20 & AC38 & AC40 & AC48 & AC50 & AC120 & _)) & (A24 & A22 & A26 & AC78 & ACc0 & _)).
cbn [rt_at rt_xv fst snd] in A8, A9, A20, A18, A21, A24, A22, A26, AC78, ACc0.
assert (Hsp : spZ regs3 = q_R (x_e rsegs cx)).
{ rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
assert (Hz : 0 <= rs_hz rsegs cx rec mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (A24' : getr regs3 (Z_to_bv 5 24) = w64 1) by (rewrite <- Hrc; exact A24).
apply (m2k_jn_walk (fx := fx3) B MT MTL cx POST ly3 S3 W3 regs3 mem3 md3 _ _ (rs_hz rsegs cx rec mod 2 ^ 32)
  Hpre Hcore Hsp A21 A24' H12 Hz A22 A26 Hhz).
intros ly4 S4 W4 regs4 mem4 md4 Hcore4 HL H22 H26 K4.
apply (HA fx3 ly4 S4 W4 regs4 mem4 md4 rec).
apply (ch_cut_A (fx := fx) B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 Hpre Hbase).
- unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; assumption.
- exact Hhz.
- ch_get HL (24%bv : bv 5). exact A24.
- exact AC78.
- exact ACc0.
- exact Hcore4.
- exact HL.
- exact H22.
- exact H26.
- exact K4.
Qed.

(* ---- KV -> FLT / MAL / JN: 0x82b14 .. 0x82b20 the type's check (decided by the shadow entry over
   [&ent[v], &ent[v] + 16)); 0x82b24 lw a1 = type; 0x82b28 li a2,6; 0x82b2c ld s6,0x78(s1); 0x82b30 ld s10,0x58(s1);
   0x82b34 beq a1,a2 -> FLT; 0x82b38 li a2,4; 0x82b3c bne a1,a2 -> MAL; Int: 0x82b40 .. 0x82b50 the size's check,
   0x82b54 lw a1 = size, 0x82b5c bltu a1,4 -> MAL; 0x82b60 .. 0x82b70 the body's check, 0x82b74 lw a2 = the body
   word, 0x82b78 j JN. No store. One entry state at KV: the real frame's cells R+0x58 / R+0x78 and the value entry's
   three words as regions (env slots 32 .. 36: the flags byte, F, the type, the size, the body word). ---- *)
Lemma m2k_val : m2k_val_stmt B MT.
Proof using MTL.
unfold m2k_val_stmt, m2k_K_val.
intros cx POST rec Hpre HMAL HFLT HJN fx3 ly3 S3 W3 regs3 mem3 md3 e a0v Hbase Hhz Hat Hent Hm.
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2_stack B cx Hpre) as (HspR & HR16 & Hrsz & Hwin & Hceil & H46 & Hsp47 & Hsp16 & Hev & Hgp & Htp).
pose proof (m2k_apart B cx Hpre) as (Hp0 & Hpc & _ & HF0 & HFc & Hc & _).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in Hceil, Hwin, Hc.
pose proof Hbase as (Hcore & Hfxk & _).
pose proof (proj1 Hcore) as HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hent as Hent0.
destruct Hent as (Hewf & Hvt & Hvs & Hvb & Hra & Ha0lo & Ha0hi & Happ).
destruct Hm as (HE0 & Hsnd & Hfst).
assert (Htr : 0 <= e_type e < 2 ^ 32) by (destruct Hewf as (H & _); lia).
assert (Hsr : 0 <= e_size e <= 45) by (destruct Hewf as (_ & _ & H); lia).
pose proof (m2k_bw_range e Hewf) as Hbr.
assert (HatA : rs_at_cx rsegs cx W3 mem3 regs3 (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec));
  (LCell XR 0x78, q_F (x_e rsegs cx)); (LCell XR 0xc0, q_pp (x_e rsegs cx))])).
{ unfold rs_at_cx, rs_at in Hat |- *. rewrite Forall_app, !Forall_cons_iff in Hat. rewrite Forall_app.
  destruct Hat as (HL & X24 & X10 & X78 & Xc0 & _). split; [exact HL|].
  repeat apply Forall_cons; try apply Forall_nil; assumption. }
unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc in Hat. rewrite Forall_app, Forall_app, !Forall_cons_iff in Hat.
destruct Hat as (((A8 & A9 & A20 & A18 & AC138 & A21 & AC18 & AC58 & _) & _) & (A24 & A10 & AC78 & ACc0 & _)).
cbn [rt_at rt_xv fst snd] in A8, A9, A20, A18, A21, AC58, A24, A10, AC78.
set (vL := q_fl (x_e rsegs cx) mod 2 ^ 64).
set (vF := q_F (x_e rsegs cx) mod 2 ^ 64).
assert (HvL : 0 <= vL < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (HvF : 0 <= vF < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (extra := [Z_to_bv 64 vL; Z_to_bv 64 vF; Z_to_bv 64 (e_type e); Z_to_bv 64 (e_size e); Z_to_bv 64 (m2k_bw e)]
  : list word).
assert (E9 : bv_unsigned (ew (Ereg regs3 extra) 9) = q_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs3 extra 9 (9%bv : bv 5) eq_refl).
  assert (G : getr regs3 9%bv = w64 (q_R (x_e rsegs cx))) by exact A9.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E10 : bv_unsigned (ew (Ereg regs3 extra) 10) = a0v).
{ rewrite (ew_Ereg_nat regs3 extra 10 (10%bv : bv 5) eq_refl).
  assert (G : getr regs3 10%bv = w64 a0v) by exact A10.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E18 : bv_unsigned (ew (Ereg regs3 extra) 18) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs3 extra 18 (18%bv : bv 5) eq_refl).
  assert (G : getr regs3 18%bv = w64 SHADOW_OFF) by exact A18.
  rewrite G. unfold w64, SHADOW_OFF. apply unsigned_lit_small. lia. }
assert (D32 : sv_denot (Ereg regs3 extra) (SOff 32 0) = Z_to_bv 64 vL)
by (apply (m2k_den_extra regs3 extra 0 vL); [reflexivity | lia]).
assert (D33 : sv_denot (Ereg regs3 extra) (SOff 33 0) = Z_to_bv 64 vF)
by (apply (m2k_den_extra regs3 extra 1 vF); [reflexivity | lia]).
assert (D34 : sv_denot (Ereg regs3 extra) (SOff 34 0) = Z_to_bv 64 (e_type e))
by (apply (m2k_den_extra regs3 extra 2 (e_type e)); [reflexivity | lia]).
assert (D35 : sv_denot (Ereg regs3 extra) (SOff 35 0) = Z_to_bv 64 (e_size e))
by (apply (m2k_den_extra regs3 extra 3 (e_size e)); [reflexivity | lia]).
assert (D36 : sv_denot (Ereg regs3 extra) (SOff 36 0) = Z_to_bv 64 (m2k_bw e))
by (apply (m2k_den_extra regs3 extra 4 (m2k_bw e)); [reflexivity | lia]).
pose (rgs := [m2_frame 0 0x80 0 0 [YP09.mkChunk 0x58 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x78 (CVal 8 (SOff 33 0))];
              m2k_ent (SOff 34 0) (SOff 35 0) (SOff 36 0)]).
assert (Hrs : Forall (region_ok rsegs (Ereg regs3 extra) (mrestrict (w_H W3) mem3)) rgs).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (m2_frame_ok _ W3 mem3 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val rsegs _ _ _ 0x58 8 (SOff 32 0) vL); [exact D32 | cbn; lia | cbn; lia | exact AC58].
    + apply (chunk_ok_val rsegs _ _ _ 0x78 8 (SOff 33 0) vF); [exact D33 | cbn; lia | cbn; lia | exact AC78].
  - apply (rtm_ro_region rsegs _ (w_H W3) mem3 10 a0v 0 16); [exact E10 | lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 34 0) (e_type e)); [exact D34 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Hvt.
    + apply (chunk_ok_val rsegs _ _ _ 4 4 (SOff 35 0) (e_size e)); [exact D35 | cbn; lia | cbn; lia | exact Hvs].
    + apply (chunk_ok_val rsegs _ _ _ 8 4 (SOff 36 0) (m2k_bw e)); [exact D36 | exact Hbr | cbn; lia | exact Hvb]. }
assert (Hpd : pairwise_disjoint (Ereg regs3 extra) rgs).
{ unfold rgs, m2k_ent, m2_frame.
  repeat split; try exact I.
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, E10. right. lia. }
assert (HG : facts_ok (Ereg regs3 extra) m2k_facts10)
  by (apply (m2k_facts10_ok _ (q_R (x_e rsegs cx)) a0v E9 ltac:(lia) HR16 E18 E10 ltac:(lia))).
pose proof (m2_entry (fx := fx3) M2K_KV [] rgs m2k_facts10 W3 regs3 extra mem3 (Forall_nil _)
  ltac:(vm_compute; reflexivity) Hrs Hpd HG) as HS.
remember (Ereg regs3 extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 extra) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx m2k_SH E (mrestrict (w_H W3) mem3)).
{ apply (m2k_sh_ok W3 mem3 E a0v);
  [ unfold M2_Bx; apply (U_atom E 18 SHADOW_OFF);
    [subst E; apply bv_eq; rewrite E18; symmetry; apply unsigned_lit_small; unfold SHADOW_OFF; lia
    | unfold SHADOW_OFF; lia]
  | apply (U_atom E 10 a0v);
    [subst E; apply bv_eq; rewrite E10; symmetry; apply unsigned_lit_small; lia | lia]
  | exact Hra | exact Happ ]. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
by (intros; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 (e_type e))
by (subst E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 (e_size e))
by (subst E; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E36 : ew E 36 = Z_to_bv 64 (m2k_bw e))
by (subst E; change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (HfF : forall regsN, getr regsN (Z_to_bv 5 22) = sv_denot E (SOff 33 0) ->
  getr regsN (Z_to_bv 5 22) = w64 (q_F (x_e rsegs cx))) by (intros regsN G; rewrite G, D33; apply m2_w64_mod).
assert (HfL : forall regsN, getr regsN (Z_to_bv 5 26) = sv_denot E (SOff 32 0) ->
  getr regsN (Z_to_bv 5 26) = w64 (q_fl (x_e rsegs cx))) by (intros regsN G; rewrite G, D32; apply m2_w64_mod).
unfold cfg_at. change (w64 M2K_KV) with (Z_to_bv 64 M2K_KV).
(* 0x82b14 .. 0x82b30, stop at 0x82b34 beq a1,a2 with a1 the type *)
m2_run m2_awr. ck_keep m2_kwr.
m2_branch Hb.
all: rewrite branch_eq_U, (m2k_U_sext32 E 34 (e_type e) E34 Htr), U_lit in Hb by lia.
- (* 0x82b34 beq taken: the type is 6, the Float arm *)
  assert (Ht6 : e_type e = POD_FLOAT).
  { apply Z.eqb_eq in Hb. apply (m2k_sx_eq _ 6 Htr ltac:(lia)) in Hb. exact Hb. }
  m2_run_to m2_awr M2K_FLT. ck_keep m2_kwr.
  m2k_rsv HS (22%bv : bv 5) G22. m2k_rsv HS (26%bv : bv 5) G26.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
    pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ m2k_L5 HS HAE ltac:(vm_compute; reflexivity)) as CL5;
    pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [10; 24]%bv HS HAE ltac:(vm_compute; reflexivity)) as C1024;
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2K_FLT by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  assert (HA : rs_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
  by (apply (m2k_run_A B MT MTL cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hhz HatA HJ);
      [ m2_io | exact C234 | exact CL5 | exact (C1024 24%bv ltac:(cbv [In]; right; left; reflexivity))
      | exact (HfF _ G22) | exact (HfL _ G26) | intros a Ha; exact (KE a Ha (fun x => x)) ]);
  apply (HFLT fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT e a0v HA)
  end.
  + etransitivity; [exact (C1024 10%bv ltac:(cbv [In]; left; reflexivity))|]. exact A10.
  + apply (m2k_ent_facts_kept W3 W3 mem3 _ e a0v); [intros a Ha; exact (KE a Ha (fun x => x)) | exact Hent0].
  + exact Ht6.
  + split; [exact HE0|]. split; [exact Hsnd | exact Hfst].
- (* not taken: the type is not 6 *)
  assert (Ht6 : e_type e <> 6).
  { intros Hc6. apply Z.eqb_neq in Hb. apply Hb. apply (m2k_sx_eq _ 6 Htr ltac:(lia)). exact Hc6. }
  m2_run m2_awr. ck_keep m2_kwr.
  m2_branch Hb2.
  all: rewrite branch_ne_U, (m2k_U_sext32 E 34 (e_type e) E34 Htr), U_lit in Hb2 by lia.
  + (* 0x82b3c bne taken: the type is neither 4 nor 6, MAL *)
    assert (Ht4 : e_type e <> 4).
    { intros Hc4. apply negb_true_iff in Hb2. apply Z.eqb_neq in Hb2. apply Hb2.
      apply (m2k_sx_eq _ 4 Htr ltac:(lia)). exact Hc4. }
    m2_run_to m2_awr M2_MAL. ck_keep m2_kwr.
    m2k_rsv HS (22%bv : bv 5) G22. m2k_rsv HS (26%bv : bv 5) G26.
    lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
      pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
      pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ m2k_L5 HS HAE ltac:(vm_compute; reflexivity)) as CL5;
      pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [24]%bv HS HAE ltac:(vm_compute; reflexivity)) as C24;
      rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
      replace (ss_pc ss) with M2_MAL by (vm_compute; reflexivity)
    end.
    assert (Hxv : Rate.expect_value e = (None, -1))
    by (apply m2k_expect_none; left; unfold POD_INT, POD_FLOAT; split; assumption).
    lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
    assert (HA : rs_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
    by (apply (m2k_run_A B MT MTL cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hhz HatA HJ);
        [ m2_io | exact C234 | exact CL5 | exact (C24 24%bv ltac:(cbv [In]; left; reflexivity))
        | exact (HfF _ G22) | exact (HfL _ G26) | intros a Ha; exact (KE a Ha (fun x => x)) ]);
    apply (HMAL fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT rec);
    apply (m2k_mal_of_A B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT HA);
    [rewrite Hfst, HE0, Hxv; reflexivity | rewrite Hsnd, HE0, Hxv; reflexivity]
    end.
  + (* not taken: the type is 4, the Int arm *)
    assert (Ht4 : e_type e = POD_INT).
    { apply negb_false_iff in Hb2. apply Z.eqb_eq in Hb2. apply (m2k_sx_eq _ 4 Htr ltac:(lia)) in Hb2. exact Hb2. }
    m2_run m2_awr. ck_keep m2_kwr.
    m2_branch Hb3.
    all: rewrite branch_ltu_U, (m2k_U_sext32 E 35 (e_size e) E35 ltac:(lia)), U_lit in Hb3 by lia.
    all: rewrite (m2k_sx_id (e_size e)) in Hb3 by lia.
    * (* 0x82b5c bltu taken: the size is below 4, MAL *)
      apply Z.ltb_lt in Hb3.
      m2_run_to m2_awr M2_MAL. ck_keep m2_kwr.
      m2k_rsv HS (22%bv : bv 5) G22. m2k_rsv HS (26%bv : bv 5) G26.
      lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
        pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
        pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ m2k_L5 HS HAE ltac:(vm_compute; reflexivity)) as CL5;
        pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [24]%bv HS HAE ltac:(vm_compute; reflexivity)) as C24;
        rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
        replace (ss_pc ss) with M2_MAL by (vm_compute; reflexivity)
      end.
      assert (Hxv : Rate.expect_value e = (None, -1)) by (apply m2k_expect_none; right; exact Hb3).
      lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
      assert (HA : rs_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
      by (apply (m2k_run_A B MT MTL cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hhz HatA HJ);
          [ m2_io | exact C234 | exact CL5 | exact (C24 24%bv ltac:(cbv [In]; left; reflexivity))
          | exact (HfF _ G22) | exact (HfL _ G26) | intros a Ha; exact (KE a Ha (fun x => x)) ]);
      apply (HMAL fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT rec);
      apply (m2k_mal_of_A B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT HA);
      [rewrite Hfst, HE0, Hxv; reflexivity | rewrite Hsnd, HE0, Hxv; reflexivity]
      end.
    * (* not taken: the size is at least 4; the body word into a2, to JN *)
      apply Z.ltb_ge in Hb3.
      m2_run_to m2_awr M2K_JN. ck_keep m2_kwr.
      m2k_rsv HS (22%bv : bv 5) G22. m2k_rsv HS (26%bv : bv 5) G26. m2k_rsv HS (12%bv : bv 5) G12.
      lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
        pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
        pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ m2k_L5 HS HAE ltac:(vm_compute; reflexivity)) as CL5;
        pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [24]%bv HS HAE ltac:(vm_compute; reflexivity)) as C24;
        rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
        replace (ss_pc ss) with M2K_JN by (vm_compute; reflexivity)
      end.
      assert (Hxv : Rate.expect_value e = (Some (Accessors.s32 (Cursor.rd32 (e_body e))), 1))
      by (apply m2k_expect_int; [exact Ht4 | exact Hb3]).
      assert (Hbw : m2k_bw e = Cursor.rd32 (e_body e)) by exact (m2k_bw_rd32 e Hewf Hb3).
      assert (Hhzv : rs_hz rsegs cx rec mod 2 ^ 32 = m2k_bw e).
      { unfold rs_hz, Rate.written_or. rewrite Hfst, HE0, Hxv. cbn [fst].
        rewrite Hbw. apply m2k_s32_mod. apply Cursor.rd32_range. }
      lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
      assert (HA : rs_cut_A (fx := fx) rsegs B MT cx fx3 rec ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
      by (apply (m2k_run_A B MT MTL cx fx3 rec ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdT Hpre Hbase Hhz HatA HJ);
          [ m2_io | exact C234 | exact CL5 | exact (C24 24%bv ltac:(cbv [In]; left; reflexivity))
          | exact (HfF _ G22) | exact (HfL _ G26) | intros a Ha; exact (KE a Ha (fun x => x)) ]);
      apply (HJN fx3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT HA)
      end.
      -- rewrite Hsnd, HE0, Hxv. reflexivity.
      -- etransitivity; [exact G12|].
         rewrite denot_lit_U, (m2k_U_sext32 E 36 (m2k_bw e) E36 Hbr), Hhzv. reflexivity.
Qed.
End k.

(* ===================================== the chain of the four pieces ===================================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* KM -> (O | KV); KV -> (FLT | MAL | JN); FLT -> (MAL | JN); JN -> A *)
Lemma m2k_chain : m2k_join_stmt B MT -> m2k_float_stmt B MT -> m2k_val_stmt B MT -> m2k_key_stmt B MT ->
rs_piece_W11b_key_stmt rsegs B MT.
Proof.
intros HJ HF HV HK. unfold rs_piece_W11b_key_stmt.
intros cx POST inp at0 m Hst HO _ HMAL HA.
pose proof Hst as (Hpre & _).
apply (HK cx POST inp at0 m Hst HO). intros rec.
apply (HV cx POST rec Hpre HMAL).
- exact (HF cx POST rec Hpre HMAL (HJ cx POST rec Hpre HA)).
- exact (HJ cx POST rec Hpre HA).
Qed.
End a.

(* ===================================== helpers of the key compare ===================================== *)
(* the registers neither run of this piece nor the wrapper writes: sp, gp, tp, s0 .. s9 *)
Definition m2kc_L : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv.
Lemma m2kc_L_cs : forall r, In r m2kc_L -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [m2kc_L In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
Lemma m2kc_cs_sub : forall (L1 L2 : list (bv 5)) ra rb, (forall r, In r L1 -> In r L2) -> cs_eq L2 ra rb -> cs_eq L1 ra rb.
Proof. intros L1 L2 ra rb HS H r Hr. exact (H r (HS r Hr)). Qed.
Ltac m2kc_in := cbv [m2kc_L m2k_L5 In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Lemma m2kc_L5_sub : forall r, In r m2k_L5 -> In r m2kc_L.
Proof. intros r Hr. cbv [m2k_L5 In] in Hr. repeat (destruct Hr as [<- | Hr]; [m2kc_in|]). destruct Hr. Qed.

Lemma m2kc_nth_skipn : forall {A : Type} (l : list A) (n i : nat) (d : A), nth (n + i) l d = nth i (skipn n l) d.
Proof.
intros A l n. revert l. induction n as [|n IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; [destruct i; reflexivity|]. cbn [Nat.add nth skipn]. apply IH.
Qed.

(* the four spill cells R+0x110 .. R+0x138 lie in M02's write set *)
Lemma m2kc_spill_E2 : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (cx : rs_scx rsegs) a,
(q_R (x_e rsegs cx) + 0x110 <= a < q_R (x_e rsegs cx) + 0x120) \/
(q_R (x_e rsegs cx) + 0x128 <= a < q_R (x_e rsegs cx) + 0x138) -> rs_E2 rsegs cx a.
Proof.
intros fx rc cx a H. left. unfold rt_inw. cbn [hi_w2 rate_himg_A].
rewrite !Exists_cons. cbn [rt_xv fst snd]. lia.
Qed.

(* facts of the run from KM: atom 9 (R) in [2^46, 2^47], 16-aligned; atom 22 (s6 = m + 1) in [1, 32], which
   decides the dead `blt a1,s11` 0x82ab0 *)
Definition m2kc_facts : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (22%nat, mkAF 1 32 0) ] [] [].
Lemma m2kc_facts_ok : forall E R v, bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 22) = v -> 1 <= v <= 32 -> facts_ok E m2kc_facts.
Proof.
intros E R v H9 HR Hal H22 Hv. split; [|split; [exact I | exact I]].
cbn [m2kc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H9, H22. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; try lia.
all: try apply Z.mod_1_r.
Qed.

Section m2kc_a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a region of a state, and the value of one of its chunks *)
Lemma m2kc_region_nth : forall H E ss ms i r,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros H E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma m2kc_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.
(* the `li s11,-1` literal; the wrapper's answer as a 64-bit word *)
Lemma m2kc_m1 : w64 18446744073709551615 = w64 (-1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma m2kc_res_range : forall c1 c2, -1 <= strcmp_res c1 c2 <= 1.
Proof.
intros c1 c2. unfold strcmp_res.
destruct (Z.eqb c1 c2); [lia|]. destruct (Z.ltb c1 c2); lia.
Qed.
Lemma m2kc_mod_zero : forall r, -1 <= r <= 1 -> (r mod 2 ^ 64 = 0 <-> r = 0).
Proof.
intros r Hr. split; intros Hz; [|subst; reflexivity].
assert (Hc : r = -1 \/ r = 0 \/ r = 1) by lia.
destruct Hc as [->|[->| ->]]; [vm_compute in Hz; discriminate | reflexivity | vm_compute in Hz; discriminate].
Qed.
End m2kc_a.

(* ===================================== FLT: the Float arm ===================================== *)
(* ===================================== the float state after the `flw` ===================================== *)
(* 0x82c78 flw fa0,0(a0): f10 holds the NaN-boxed binary32 b, the rest of f is kept *)
Definition m2kf_fx4 (f : YK11.FPState) (b : Z) : YK11.FPState :=
YK11.mkFP (bvmap_set (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b)) (@fp_regs f)) (@fp_csr f).

Lemma m2kf_fxk_trans : forall ks ks' f g h,
rt_fxk ks f g -> rt_fxk ks' g h -> (forall z, In z ks' -> In z ks) -> rt_fxk ks f h.
Proof.
intros ks ks' f g h (Hg & _) (Hh & Hcsr) Hin. split; [|exact Hcsr].
intros k Hk. rewrite (Hh k ltac:(intros Hc; exact (Hk (Hin _ Hc)))). exact (Hg k Hk).
Qed.

Lemma m2kf_fxk_set : forall ks f g b, In 10 ks -> rt_fxk ks f g -> rt_fxk ks f (m2kf_fx4 g b).
Proof.
intros ks f g b Hr (Hg & Hcsr). split; [|exact Hcsr].
intros k Hk. unfold m2kf_fx4. cbn [fp_regs].
destruct (base.decide (k = Z_to_bv 5 10)) as [->|Hne]; [exfalso; exact (Hk Hr)|].
change (bvmap_set (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b)) (@fp_regs g))
  with (regupd (@fp_regs g) (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b))).
rewrite (regupd_other (@fp_regs g) (Z_to_bv 5 10) (nan_box (Z_to_bv 32 b)) k Hne). exact (Hg k Hk).
Qed.

Lemma m2kf_f10 : forall f b, Sem.reg_get (@fp_regs (m2kf_fx4 f b)) (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b).
Proof. intros f b. unfold m2kf_fx4. cbn [fp_regs]. apply regupd_same. Qed.

(* the low 4 bytes of an 8-byte cell *)
Lemma m2kf_val_lo4 : forall m a v, val_mem rsegs m a 8 v -> val_mem rsegs m a 4 (v mod 2 ^ 32).
Proof.
intros m a v H k Hk. rewrite (H k ltac:(lia)). f_equal.
rewrite !rtm_le_byte_bv by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
apply Z.bits_inj'. intros i Hi. destruct (Z_lt_le_dec i 8) as [Hl|Hg].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* ===================================== the `flw` ===================================== *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* 0x82c78 flw fa0,0(a0) with a0 = a and the 4 bytes at a holding b; the walk goes on at 0x82c7c *)
Lemma m2kf_flw : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) a b,
getr regs (Z_to_bv 5 10) = Z_to_bv 64 a ->
val_mem rsegs (mrestrict (w_H W) mem) a 4 b -> 0 <= b < 2 ^ 32 ->
(forall md', same_but_materialized md md' -> SRr rsegs W (@cfg_at (m2kf_fx4 fx b) rsegs 0x82c7c regs mem md') Q) ->
SRr rsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 0x82c78) mem (seg_rom rsegs)) md) Q.
Proof.
intros W regs mem md Q a b H10 Hval Hb HK.
assert (Hrd : rdn rsegs (mrestrict (w_H W) mem) (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 b)).
{ apply (proj2 (YP09.rdn_mbytes rsegs _ _ _ _)). split; [apply length_Z_to_le_bytes|].
  intros i Hi. rewrite (Hval i Hi).
  rewrite (nth_error_nth' (Z_to_le_bytes 4 b) (Z_to_bv 8 0)) by (rewrite length_Z_to_le_bytes; exact Hi).
  rewrite rtm_nth_le_bytes by exact Hi. rewrite rtm_le_byte_bv by exact Hi. reflexivity. }
assert (Hw : bv_extract 0 32 (le_bytes_to_word (Z_to_le_bytes 4 b)) = Z_to_bv 32 b).
{ rewrite le_bytes_to_word_Z, Cursor.bytes_le_to_Z_Z_to_le_bytes.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small b (2 ^ 32)) by lia.
  apply bv_eq. rewrite bv_extract_unsigned, unsigned_lit_small by lia. rewrite Z_to_bv_unsigned.
  try (f_equal; apply Z.shiftr_0_r). }
eapply (SRr_step rsegs ck_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (YK0o.fp_step_flw fx rsegs regs (Z_to_bv 64 0x82c78) (mrestrict (w_H W) mem) (seg_rom rsegs)
    (Z_to_bv 32 0x52507) (Z_to_bv 5 10) (Z_to_bv 5 10) (Z_to_bv 12 0) (Z_to_bv 64 a) (Z_to_le_bytes 4 b));
  [ reflexivity | vm_refl_bv | vm_compute; reflexivity | vm_refl_bv
  | rewrite H10; replace (bv_signed (Z_to_bv 12 0)) with 0 by reflexivity; apply v_addi_0
  | exact Hrd ].
- intros md' Hsame. rewrite unrestrict_mkst_mrestrict, Hw.
  replace (v_addi (Z_to_bv 64 0x82c78) 4) with (w64 0x82c7c) by reflexivity.
  exact (HK md' Hsame).
Qed.
End s.

(* ===================================== the three runs ===================================== *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HNEAR : forall fy : YK11.FPState, rt_pod_nearest_specX (fx := fy) rsegs B MT M2_A_NEAREST.

(* 0x82c44 .. 0x82c74: the size test, then the `flw` *)
Lemma m2kf_walk1 : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2
  a0v sz bw,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)) -> getr regs2 (Z_to_bv 5 18) = w64 SHADOW_OFF ->
getr regs2 (Z_to_bv 5 10) = w64 a0v -> 4096 <= a0v -> a0v + 16 <= alloc_ceiling ->
(a0v + 16 <= kLowShadowBeg \/ kHighMemBeg <= a0v) ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF a0v 16 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 4) 4 sz -> 0 <= sz < 2 ^ 31 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (a0v + 8) 4 bw -> 0 <= bw < 2 ^ 32 ->
(sz < 4 -> forall regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W2 (@cfg_at fx rsegs M2_MAL regs3 mem3 md3) POST) ->
(4 <= sz -> forall regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W2 (@cfg_at (m2kf_fx4 fx bw) rsegs 0x82c7c regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs M2K_FLT regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST ly2 S2 W2 regs2 mem2 md2 a0v sz bw Hpre Hcore H9 H18 H10 Ha1 Ha2 Happ Hra Hsz Hsz' Hbw Hbw'
  KMAL KF.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (E9 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 9 = Z_to_bv 64 (q_R (x_e rsegs cx)))
by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
assert (E18 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 18 = Z_to_bv 64 SHADOW_OFF)
by (rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl); exact H18).
assert (E10 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 10 = Z_to_bv 64 a0v)
by (rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 32 = Z_to_bv 64 sz)
by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) 33 = Z_to_bv 64 bw)
by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
pose proof (m2_entry (fx := fx) M2K_FLT []
  [YP09.mkRegion (Some 10%nat) 4 12 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0))]]
  m2k_facts10 W2 regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw] mem2 (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (rtm_ro_region rsegs _ (w_H W2) mem2 10 a0v 4 12);
  [ rewrite E10; apply unsigned_lit_small; lia | lia | lia |
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    [ apply (chunk_ok_val rsegs _ _ a0v 4 4 (SOff 32 0) sz);
      [ apply m2k_denot_of_U; apply U_atom; [exact E32 | lia] | cbn; lia | cbn; lia | exact Hsz ]
    | apply (chunk_ok_val rsegs _ _ a0v 8 4 (SOff 33 0) bw);
      [ apply m2k_denot_of_U; apply U_atom; [exact E33 | lia] | exact Hbw' | cbn; lia | exact Hbw ] ] ])).
specialize (HS ltac:(cbn; tauto)).
specialize (HS (m2k_facts10_ok (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) (q_R (x_e rsegs cx)) a0v
  ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
  ltac:(rewrite E18; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
  ltac:(rewrite E10; apply unsigned_lit_small; lia) ltac:(lia))).
assert (SHOK : sh_ok rsegs M2_Bx m2k_SH (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) (mrestrict (w_H W2) mem2)).
{ apply (m2k_sh_ok W2 mem2 _ a0v); [| | exact Hra | exact Happ].
  - unfold M2_Bx. apply U_atom; [exact E18 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E10 | lia]. }
remember (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 sz; Z_to_bv 64 bw]) E) by (subst E; apply env_agree_refl).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 M2K_FLT) with (Z_to_bv 64 M2K_FLT).
(* 0x82c44 .. 0x82c5c, stop at 0x82c60 bltu size,4 *)
m2_run m2_awr. ck_keep m2_kwr.
m2_branch Hb.
all: rewrite branch_ltu_U, (m2k_U_sext32 E 32 sz E32 ltac:(lia)), U_lit, (m2k_sx_id sz Hsz') in Hb by lia.
- (* taken: the size is below 4, to MAL *)
  assert (Hlt : sz < 4) by (apply Z.ltb_lt; exact Hb).
  m2_run_to m2_awr M2_MAL. ck_keep m2_kwr.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (Hpr : aregs_preserved regs2 (ms_regs ms))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2_MAL by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KMAL Hlt (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ intros r Hr; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | m2_io
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
  | exact Hpr
  | intros a Ha; exact (KE a Ha (fun x => x)) ]
  end.
- (* not taken: the body word, then the `flw` *)
  assert (Hge : 4 <= sz) by (apply Z.ltb_ge; exact Hb).
  m2_run m2_awr. ck_keep m2_kwr.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msT end.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H msT), HAE : env_agree 32 _ ?E |- _ =>
    assert (G10 : getr (ms_regs msT) (Z_to_bv 5 10) = Z_to_bv 64 (a0v + 8))
    by (rewrite (st_ok_restrict_reg rsegs H E ss msT (Z_to_bv 5 10) HS);
        replace (sr_get (ss_regs ss) (Z_to_bv 5 10)) with (SOff 10 8) by (vm_compute; reflexivity);
        apply m2k_denot_of_U; apply U_atom_off; [exact E10 | lia | lia]);
    assert (Hpr : aregs_preserved regs2 (ms_regs msT))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss msT HS eq_refl);
    replace (ss_pc ss) with 0x82c78 by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msT) ?mdT _ |- _ =>
  apply (m2kf_flw W2 (ms_regs msT) (ms_mem msT) mdT POST (a0v + 8) bw G10);
  [ apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 (ms_mem msT) (a0v + 8) 4 bw); [|exact Hbw];
    intros k Hk; cbn in Hk; exact (KE (a0v + 8 + k) ltac:(lia) (fun x => x))
  | exact Hbw'
  | intros md' Hsame; rewrite (same_but_materialized_wvb mdT md' Hsame);
    apply (KF Hge (ms_regs msT) (ms_mem msT));
    [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msT) (ms_mem msT) _ Hcore);
      [ eapply ajournal_materialize; eassumption
      | intros r Hr; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | m2_io
      | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
    | exact Hpr
    | intros a Ha; exact (KE a Ha (fun x => x)) ] ]
  end.
Qed.

(* the out cell R + 0x158 of pod_nearest: its 8 bytes are marked usable at every state of the segment (hi_rz at
   the segment's start; the shadow bytes lie in the high shadow, below R - T_SEG_STK and apart from rs_E2) *)
Lemma m2kf_ra_out : forall (cx : rs_scx rsegs) ly4 S4 W4 regs4 mem4 md4,
rs_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly4 S4 W4 regs4 mem4 md4 ->
range_addressable (aview rsegs (w_H W4) mem4) SHADOW_OFF (q_R (x_e rsegs cx) + 0x158) 8.
Proof.
intros cx ly4 S4 W4 regs4 mem4 md4 Hpre Hpod Hcore.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & _).
pose proof (m2_frameF B cx Hpre) as (F32 & F4096 & Fceil & Fapp & _).
pose proof asan_consts as (C1 & _).
pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
destruct Hp as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrz & _).
cbn [hi_rz rate_himg_A] in Hrz. rewrite Forall_cons_iff in Hrz. destruct Hrz as (Hrz & _). cbn [fst snd] in Hrz.
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpod) as (_ & P4096 & Pceil & Papp & _).
assert (Hreq : q_len (x_e rsegs cx) <= req_size (q_len (x_e rsegs cx)))
by (unfold req_size; destruct (Z.eqb_spec (q_len (x_e rsegs cx)) 0); lia).
destruct Hcore as (_ & _ & _ & _ & _ & _ & HK).
intros x Hx. destruct (Hrz x ltac:(lia)) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
rewrite <- Hsv.
assert (L1 : 2 ^ 43 <= x / 8) by (apply Z.div_le_lower_bound; lia).
assert (L2 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as DF.
pose proof (Z.mod_pos_bound (q_F (x_e rsegs cx)) 8 ltac:(lia)) as MF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Papp.
apply HK.
- unfold shadow_of_addr, SHADOW_OFF. lia.
- rewrite HR. unfold shadow_of_addr, SHADOW_OFF, T_SEG_STK, ASTACK. lia.
- unfold rs_E2, rt_inw. cbn [hi_w2 rate_himg_A]. intros [Hw|Hw].
  + rewrite !Exists_cons, Exists_nil in Hw. cbn [rt_xv fst snd] in Hw.
    unfold shadow_of_addr, shadow_addr, SHADOW_OFF, T_SEG_STK, ASTACK in *.
    destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]]]]]]; lia.
  + unfold shadow_of_addr, SHADOW_OFF in Hw. lia.
Qed.

(* 0x82c7c .. 0x82c80 at the float state after the `flw`, then pod_nearest *)
Lemma m2kf_walk2 : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2 b,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
getr regs2 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)) ->
0 <= b < 2 ^ 32 -> Sem.reg_get (@fp_regs fx) (Z_to_bv 5 10) = Sem.nan_box (Z_to_bv 32 b) ->
YK0o.frm_zero (@fp_csr fx) ->
(forall (fx3 : YK11.FPState) ly3 S3 W3 regs3 mem3 md3,
  rt_fxk [15] fx fx3 ->
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  getr regs3 (Z_to_bv 5 10) = w64 (rt_near_rc (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX)) ->
  match Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX with
  | Some r => val_mem rsegs (mrestrict (w_H W3) mem3) (q_R (x_e rsegs cx) + 0x158) 8 (r mod 2 ^ 64)
  | None => True
  end ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_nearest_STK <= a < q_R (x_e rsegs cx)) ->
   ~ (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
      q_R (x_e rsegs cx) + 0x158 <= a < q_R (x_e rsegs cx) + 0x158 + 8) ->
   aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W3 (@cfg_at fx3 rsegs 0x82c84 regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs 0x82c7c regs2 mem2 md2) POST.
Proof using MTL HNEAR.
intros cx POST ly2 S2 W2 regs2 mem2 md2 b Hpre Hcore Hpod H9 Hb HF10 Hfrm KN.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (Hsp : spZ regs2 = q_R (x_e rsegs cx)).
{ rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
assert (E9 : ew (Ereg regs2 []) 9 = Z_to_bv 64 (q_R (x_e rsegs cx)))
by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
pose proof (m2_entry (fx := fx) 0x82c7c [] [] (mkFacts [] [] []) W2 regs2 [] mem2 (Forall_nil _) eq_refl
  (Forall_nil _) I ltac:(repeat split)) as HS.
remember (Ereg regs2 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 0x82c7c) with (Z_to_bv 64 0x82c7c).
(* 0x82c7c addi a0,s1,0x158; 0x82c80 jal pod_nearest: stop at 0x83dc0 *)
m2_run m2_awr. ck_keep m2_kwr.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msT end.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H msT), HAE : env_agree 32 _ ?E |- _ =>
  assert (G10 : getr (ms_regs msT) (Z_to_bv 5 10) = w64 (q_R (x_e rsegs cx) + 0x158))
  by (rewrite (st_ok_restrict_reg rsegs H E ss msT (Z_to_bv 5 10) HS);
      replace (sr_get (ss_regs ss) (Z_to_bv 5 10)) with (SOff 9 0x158) by (vm_compute; reflexivity);
      apply m2k_denot_of_U; apply U_atom_off; [exact E9 | lia | lia]);
  assert (G1 : getr (ms_regs msT) 1 = w64 0x82c84)
  by (rewrite (st_ok_restrict_reg rsegs H E ss msT 1%bv HS);
      replace (sr_get (ss_regs ss) 1%bv) with (SLit 0x82c84) by (vm_compute; reflexivity);
      reflexivity);
  assert (Hpr : aregs_preserved regs2 (ms_regs msT))
  by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
  rewrite (st_ok_restrict_mkst rsegs H E ss msT HS eq_refl);
  replace (ss_pc ss) with M2_A_NEAREST by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs msT) = q_R (x_e rsegs cx)) by (rewrite (m2_sp_pres _ _ Hpr); exact Hsp).
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msT) ?mdT _ |- _ =>
assert (HcoreT : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT)
by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msT) (ms_mem msT) mdT Hcore HJ);
    [ intros r Hr; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | m2_io
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ])
end.
assert (HEc : forall a, (Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
  q_R (x_e rsegs cx) + 0x158 <= a < q_R (x_e rsegs cx) + 0x158 + 8) -> rs_E2 rsegs cx a).
{ intros a (_ & Ha). left. unfold rt_inw. cbn [hi_w2 rate_himg_A].
  rewrite !Exists_cons. cbn [rt_xv fst snd].
  right. right. right. right. right. right. right. right. left. lia. }
eapply SRr_bind.
{ apply (HNEAR fx (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem msT) _ (x_k rsegs cx) (ms_regs msT)
    (q_R (x_e rsegs cx) + 0x158) b).
  - apply (m2_pre_call B MT cx _ _ _ _ _ _ _ T_nearest_STK Hpre HcoreT);
    [ rewrite G1; vm_compute; reflexivity
    | unfold raZ; rewrite G1; unfold w64; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_nearest_STK, T_SEG_STK, ASTACK; lia ].
  - exact G10.
  - exact Hb.
  - exact HF10.
  - unfold rt_wcell. rewrite HspT. unfold T_SEG_STK, ASTACK in *. split; [left; split; lia | left; lia].
  - pose proof (Z.div_mod (q_R (x_e rsegs cx)) 16 ltac:(lia)) as D. rewrite Hal in D.
    replace (q_R (x_e rsegs cx) + 0x158) with ((2 * (q_R (x_e rsegs cx) / 16) + 43) * 8) by lia.
    apply Z_mod_mult.
  - exact (m2kf_ra_out cx ly2 S2 W2 (ms_regs msT) (ms_mem msT) _ Hpre Hpod HcoreT).
  - exact (m2_rom_at B MT cx ly2 S2 W2 (ms_regs msT) (ms_mem msT) _ Hpre Hpod HcoreT).
  - exact Hfrm. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (rs_E2 rsegs cx)
  (fun x => Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX <> None /\
     q_R (x_e rsegs cx) + 0x158 <= x < q_R (x_e rsegs cx) + 0x158 + 8) T_nearest_STK ly2 S2 W2 (ms_regs msT)
  (ms_mem msT) _ _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK; lia) HEc Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & Hrc3).
subst c3. rewrite G1. destruct Hrc3 as (H10' & Hval').
apply (KN fx3 ly3 S3 W3 regs3 mem3 md3 Hfx3 Hcore3 (aregs_preserved_trans _ _ _ Hpr Hpres3) H10' Hval').
intros a Ha Hs Hn. rewrite (Hkept3 a Ha Hs Hn). exact (KE a Ha (fun x => x)).
Qed.

(* 0x82c84 beqz a0 -> MAL; 0x82c88 lw a2,0x158(s1); to JN 0x82c8c *)
Lemma m2kf_walk3 : forall (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) ly2 S2 W2 regs2 mem2 md2
  (o : option Z),
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)) ->
getr regs2 (Z_to_bv 5 10) = w64 (rt_near_rc o) ->
match o with
| Some r => val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x158) 8 (r mod 2 ^ 64)
| None => True
end ->
(o = None -> forall regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  SRr rsegs W2 (@cfg_at fx rsegs M2_MAL regs3 mem3 md3) POST) ->
(forall r, o = Some r -> forall regs3 mem3 md3,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 -> aregs_preserved regs2 regs3 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  getr regs3 (Z_to_bv 5 12) = w64 (m2k_sx (r mod 2 ^ 32)) ->
  SRr rsegs W2 (@cfg_at fx rsegs M2K_JN regs3 mem3 md3) POST) ->
SRr rsegs W2 (@cfg_at fx rsegs 0x82c84 regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST ly2 S2 W2 regs2 mem2 md2 o Hpre Hcore H9 H10 Hval KN KS.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof asan_consts as (C1 & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (proj1 Hcore) as HJ.
destruct o as [r|].
- (* Some r: the `beqz` is not taken; a2 = the low word of the 8 bytes at R + 0x158, sign-extended *)
  assert (Hr32 : 0 <= r mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Hval4 : val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x158) 4 (r mod 2 ^ 32)).
  { pose proof (m2kf_val_lo4 _ _ _ Hval) as V.
    replace (r mod 2 ^ 64 mod 2 ^ 32) with (r mod 2 ^ 32) in V; [exact V|].
    symmetry. apply (Z.mod_mod_divide r (2 ^ 64) (2 ^ 32)). exists (2 ^ 32). reflexivity. }
  assert (E9 : ew (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 32)]) 9 = Z_to_bv 64 (q_R (x_e rsegs cx)))
  by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
  assert (E32 : ew (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 32)]) 32 = Z_to_bv 64 (r mod 2 ^ 32))
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  pose proof (m2_entry (fx := fx) 0x82c84 [((10%bv : bv 5), SLit 1)]
    [m2_frame 0x158 0x15c 0 0 [YP09.mkChunk 0x158 (CVal 4 (SOff 32 0))]] m2_facts W2 regs2
    [Z_to_bv 64 (r mod 2 ^ 32)] mem2) as HS.
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
    [ intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
    | rewrite ck_lit; symmetry; exact H10 ]) eq_refl).
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; unfold m2_frame;
    apply (rtm_ro_region rsegs _ (w_H W2) mem2 9 (q_R (x_e rsegs cx)) 0x158 0x15c);
    [ rewrite E9; apply unsigned_lit_small; lia | lia | lia |
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val rsegs _ _ (q_R (x_e rsegs cx)) 0x158 4 (SOff 32 0) (r mod 2 ^ 32));
      [ apply m2k_denot_of_U; apply U_atom; [exact E32 | lia] | cbn; lia | cbn; lia | exact Hval4 ] ])).
  specialize (HS ltac:(cbn; tauto)
    (m2_facts_ok (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 32)]) (q_R (x_e rsegs cx))
      ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal)).
  remember (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 32)]) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 (r mod 2 ^ 32)]) E) by (subst E; apply env_agree_refl).
  assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
  unfold cfg_at. change (w64 0x82c84) with (Z_to_bv 64 0x82c84).
  m2_run_to m2_awr M2K_JN. ck_keep m2_kwr.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (G12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (m2k_sx (r mod 2 ^ 32)))
    by (rewrite (st_ok_restrict_reg rsegs H E ss ms (Z_to_bv 5 12) HS);
        replace (sr_get (ss_regs ss) (Z_to_bv 5 12)) with (SExt true 32 (SOff 32 0)) by (vm_compute; reflexivity);
        apply m2k_denot_of_U; apply (m2k_U_sext32 E 32 (r mod 2 ^ 32) E32 Hr32));
    assert (Hpr : aregs_preserved regs2 (ms_regs ms))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2K_JN by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KS r eq_refl (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ intros q Hq; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | m2_io
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
  | exact Hpr
  | intros a Ha; exact (KE a Ha (fun x => x))
  | exact G12 ]
  end.
- (* None: the `beqz` is taken, to MAL *)
  pose proof (m2_entry (fx := fx) 0x82c84 [((10%bv : bv 5), SLit 0)] [] (mkFacts [] [] []) W2 regs2 [] mem2) as HS.
  specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
    [ intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
    | rewrite ck_lit; symmetry; exact H10 ]) eq_refl (Forall_nil _) I ltac:(repeat split)).
  remember (Ereg regs2 []) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
  assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
  unfold cfg_at. change (w64 0x82c84) with (Z_to_bv 64 0x82c84).
  m2_run_to m2_awr M2_MAL. ck_keep m2_kwr.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
    assert (Hpr : aregs_preserved regs2 (ms_regs ms))
    by (eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]);
    rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
    replace (ss_pc ss) with M2_MAL by (vm_compute; reflexivity)
  end.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (KN eq_refl (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ);
    [ intros q Hq; apply Hpr; unfold acallee_saved; lia | reflexivity | apply Permutation_refl | m2_io
    | apply (mo_le_refl MT MTL) | intros a Ha _ _; exact (KE a Ha (fun x => x)) ]
  | exact Hpr
  | intros a Ha; exact (KE a Ha (fun x => x)) ]
  end.
Qed.
End w.

(* ===================================== the callees' contracts at any float state ===================================== *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
(* the two cells of the runtime's symbol record pod_nearest's code reads (as lib/A/RtPgCheckCode.v and
   lib/A/RtPgRefuse.v take them): the .got slot of the shadow offset and the cell it names *)
Hypothesis HGOT : as_got_shadow B = 0x9be70.
Hypothesis HSC : as_shadow_cell B = 0xa4c38.
(* the strcmp wrapper's contract (lib/Reusable/AStrcmpDef.v) at every float state: the key compare calls it at
   the cut's float state, which is not the segment's *)
Hypothesis ASTRCMP : forall fy : YK11.FPState, astrcmp_realizes (fx := fy) rsegs B M2_STRCMP.

(* pod_nearest 0x83dc0 at every float state (lib/A/RtPgNearA.v rt_pod_nearest_A): the Float arm calls it at the
   float state the `flw` leaves *)
Lemma m2k_near : forall fy : YK11.FPState, rt_pod_nearest_specX (fx := fy) rsegs B MT M2_A_NEAREST.
Proof using MTL HGOT HSC.
intros fy. exact (RtPgNearA.rt_pod_nearest_A (fx := fy) B MT MTL (AR_laws_ok rsegs B) HGOT HSC).
Qed.

(* ---- FLT -> MAL / JN ---- *)
Lemma m2k_float : m2k_float_stmt B MT.
Proof using MTL HGOT HSC.
unfold m2k_float_stmt, m2k_K_float.
intros cx POST rec Hpre HMAL HJOIN fx3 ly3 S3 W3 regs3 mem3 md3 e a0v HA H10 Hent Hty Hm.
pose proof HA as (Hbase & Hat & Hhz).
pose proof Hbase as (Hcore & Hfxk & _ & _ & _ & _ & _ & _ & Hpod & _).
destruct Hent as (Hewf & _ & Hvs & Hvb & Hra & Ha1 & Ha2 & Happ).
pose proof Hewf as (Hwt & Hwb & Hws).
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & _).
pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_chk, rs_Hc in Hat'.
rewrite Forall_app, Forall_app, !Forall_cons_iff in Hat'.
destruct Hat' as (((A8 & A9 & A20 & A18 & AC138 & A21 & AC18 & AC58 & _) &
                   (AC20 & AC38 & AC40 & AC48 & AC50 & AC120 & _)) & (A24 & A22 & A26 & AC78 & ACc0 & _)).
cbn [rt_at rt_xv fst snd] in A9, A18, A24, A22, A26, AC78, ACc0.
assert (HatA : rs_at_cx rsegs cx W3 mem3 regs3
  (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec));
                        (LCell XR 0x78, q_F (x_e rsegs cx)); (LCell XR 0xc0, q_pp (x_e rsegs cx))])).
{ unfold rs_at_cx, rs_at in Hat |- *. rewrite Forall_app in Hat |- *. destruct Hat as (HL1 & HL2).
  split; [exact HL1|]. rewrite !Forall_cons_iff in HL2. destruct HL2 as (X24 & _ & _ & X78 & Xc0 & _).
  apply Forall_cons; [exact X24|]. apply Forall_cons; [exact X78|]. apply Forall_cons; [exact Xc0 | apply Forall_nil]. }
assert (HPA : rs_PA rsegs cx rec = Rate.expect_value e).
{ destruct Hm as (HE0 & HPs & HPf).
  rewrite <- HE0, (surjective_pairing (rs_PA rsegs cx rec)), HPf, HPs. symmetry. apply surjective_pairing. }
assert (HwzK : forall a, ~ m2k_wz cx a -> 0 <= a < 2 ^ 64 -> True) by (intros; exact I).
(* the exit to A's cut, from the cut at FLT, at a state whose callee-saved registers are kept, whose memory agrees
   outside m2k_wz and whose float state keeps fx outside fa0, fa3, fa4, fa5 *)
assert (XA : forall (fx5 : YK11.FPState) ly5 S5 W5 regs5 mem5 md5,
  rs_core rsegs B MT cx (rs_E2 rsegs cx) ly5 S5 W5 regs5 mem5 md5 -> aregs_preserved regs3 regs5 ->
  rt_fxk [10; 13; 14; 15] fx fx5 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ m2k_wz cx a -> aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W3) mem3 a) ->
  rs_cut_A (fx := fx) rsegs B MT cx fx5 rec ly5 S5 W5 regs5 mem5 md5).
{ intros fx5 ly5 S5 W5 regs5 mem5 md5 Hcore5 Hpr5 Hfxk5 K5.
  apply (m2k_cut_A B MT cx fx3 fx5 rec ly3 S3 W3 regs3 mem3 md3 ly5 S5 W5 regs5 mem5 md5 Hpre Hbase Hhz HatA
    Hcore5 Hfxk5 (cs_eq_of_pres m2k_L5 _ _ m2k_L5_cs Hpr5)).
  - exact (Hpr5 24 ltac:(unfold acallee_saved; lia)).
  - rewrite (Hpr5 22 ltac:(unfold acallee_saved; lia)). exact A22.
  - rewrite (Hpr5 26 ltac:(unfold acallee_saved; lia)). exact A26.
  - exact K5. }
apply (m2kf_walk1 (fx := fx3) B MT MTL cx POST ly3 S3 W3 regs3 mem3 md3 a0v (e_size e) (m2k_bw e) Hpre Hcore
  A9 A18 H10 Ha1 Ha2 Happ Hra Hvs ltac:(lia) Hvb (m2k_bw_range e Hewf)).
- (* the size is below 4: MAL *)
  intros Hlt regs4 mem4 md4 Hcore4 Hpr4 K4.
  apply (HMAL fx3 ly3 S3 W3 regs4 mem4 md4 rec).
  apply m2k_mal_of_A.
  + apply (XA fx3 ly3 S3 W3 regs4 mem4 md4 Hcore4 Hpr4 Hfxk). intros a Ha _. exact (K4 a Ha).
  + rewrite HPA, m2k_expect_none; [reflexivity | right; exact Hlt].
  + rewrite HPA, m2k_expect_none; [reflexivity | right; exact Hlt].
- (* the body word in fa0, then pod_nearest *)
  intros Hge regs4 mem4 md4 Hcore4 Hpr4 K4.
  assert (Hfxk4 : rt_fxk [10; 13; 14; 15] fx (m2kf_fx4 fx3 (m2k_bw e)))
  by (apply m2kf_fxk_set; [left; reflexivity | exact Hfxk]).
  apply (m2kf_walk2 (fx := m2kf_fx4 fx3 (m2k_bw e)) B MT MTL m2k_near cx POST ly3 S3 W3 regs4 mem4 md4 (m2k_bw e)
    Hpre Hcore4 Hpod ltac:(rewrite (Hpr4 9 ltac:(unfold acallee_saved; lia)); exact A9) (m2k_bw_range e Hewf)
    (m2kf_f10 fx3 (m2k_bw e)) (proj2 Hfxk)).
  intros fx5 ly5 S5 W5 regs5 mem5 md5 Hfx5 Hcore5 Hpr5 H10' Hval' K5.
  assert (Hfxk5 : rt_fxk [10; 13; 14; 15] fx fx5)
  by (apply (m2kf_fxk_trans _ _ _ _ _ Hfxk4 Hfx5); intros z Hz; cbn in Hz |- *; tauto).
  assert (Hpr35 : aregs_preserved regs3 regs5) by exact (aregs_preserved_trans _ _ _ Hpr4 Hpr5).
  apply (m2kf_walk3 (fx := fx5) B MT MTL cx POST ly5 S5 W5 regs5 mem5 md5
    (Nearest.nearest (m2k_bw e) Nearest.INT32_MIN Nearest.INT32_MAX) Hpre Hcore5
    ltac:(rewrite (Hpr35 9 ltac:(unfold acallee_saved; lia)); exact A9) H10' Hval').
  + (* None: MAL *)
    intros Hn regs6 mem6 md6 Hcore6 Hpr6 K6.
    apply (HMAL fx5 ly5 S5 W5 regs6 mem6 md6 rec).
    assert (HPA' : rs_PA rsegs cx rec = (None, -1)).
    { rewrite HPA, (m2k_expect_float e Hty Hge), <- (m2k_bw_rd32 e Hewf Hge), Hn. reflexivity. }
    apply m2k_mal_of_A; [| rewrite HPA'; reflexivity | rewrite HPA'; reflexivity].
    apply (XA fx5 ly5 S5 W5 regs6 mem6 md6 Hcore6 (aregs_preserved_trans _ _ _ Hpr35 Hpr6) Hfxk5).
    intros a Ha Hw. unfold m2k_wz in Hw.
    rewrite (K6 a Ha), (K5 a Ha ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK in *; lia)
      ltac:(intros (Hne & _); exact (Hne Hn))).
    exact (K4 a Ha).
  + (* Some r: the join *)
    intros r Hr regs6 mem6 md6 Hcore6 Hpr6 K6 H12.
    assert (HPA' : rs_PA rsegs cx rec = (Some r, 1)).
    { rewrite HPA, (m2k_expect_float e Hty Hge), <- (m2k_bw_rd32 e Hewf Hge), Hr. reflexivity. }
    apply (HJOIN fx5 ly5 S5 W5 regs6 mem6 md6).
    * apply (XA fx5 ly5 S5 W5 regs6 mem6 md6 Hcore6 (aregs_preserved_trans _ _ _ Hpr35 Hpr6) Hfxk5).
      intros a Ha Hw. unfold m2k_wz in Hw.
      rewrite (K6 a Ha), (K5 a Ha ltac:(unfold T_nearest_STK, T_SEG_STK, ASTACK in *; lia)
        ltac:(intros (_ & Hx); lia)).
      exact (K4 a Ha).
    * rewrite HPA'. reflexivity.
    * rewrite H12. unfold rs_hz, Rate.written_or. rewrite HPA'. reflexivity.
Qed.

(* ---- KM -> O / KV ---- *)
(* the key ent[m]'s text at &ent[m].body = pp + 0x401c + 104 m, NUL-terminated inside the first block, with the
   wrapper's range premises on its 46 bytes *)
Lemma m2kc_key_str : forall (cx : rs_scx rsegs) (fx2 : YK11.FPState) rec ly2 S2 W2 regs2 mem2 md2 (m : nat) kb,
rs_pre rsegs B cx -> rs_chk_base (fx := fx) rsegs B MT cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 ->
(m < length (ents rec))%nat -> key_of (nth m (ents rec) m2k_d) = Some kb ->
cstr_at rsegs W2 mem2 (q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) (map (fun b : byte => bv_unsigned b) kb) /\
(length kb < 45)%nat /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) 46 /\
shadow_hull_vis (aview rsegs (w_H W2) mem2) (q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) 46 /\
amem_range (q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) 46.
Proof.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 m kb Hpre (Hcore & _ & _ & _ & Hpp & Hwf & _) Hml Hk.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2k_apart B cx Hpre) as (Hp0 & Hpc & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (m2k_nent_le rec Hwf) as Hn32.
pose proof (m2k_ent_wf_nth rec m Hwf Hml) as Hewf.
destruct (m2k_key_of_some _ _ Hk) as (Hkb & _ & Hs1 & Hnul).
set (e := nth m (ents rec) m2k_d) in *.
pose proof (m2k_ent_mem_len e Hewf) as HL.
pose proof Hewf as (Htr & Hbl & Hsz).
assert (Hk0 : (Z.to_nat (e_size e - 1) < length (e_body e))%nat) by lia.
destruct (m2k_cstr_bytes (e_body e) _ Hk0 Hnul) as (Hcl & Hci & Hcn).
rewrite <- Hkb in Hcl, Hci, Hcn.
assert (B0 : rtm_bytes rsegs (w_H W2) mem2 (q_pp (x_e rsegs cx)) (Layout.pp_bytes rec)) by exact Hpp.
unfold Layout.pp_bytes in B0.
pose proof (rtm_pp_ent rsegs (Model.buf rec) (Model.is_props rec) (Model.has_params rec)
  (Model.params_struct rec) (Model.ents rec) (Model.corrupt rec) (m2k_buf_max rec Hwf) Hn32
  (m2k_bodies_96 rec Hwf) (w_H W2) mem2 (q_pp (x_e rsegs cx)) m B0 Hml) as BE.
change (Model.Ent 0 0 []) with m2k_d in BE. fold e in BE.
rewrite rtm_bytes_aview in BE.
set (x := q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m).
assert (Hbyte : forall i, (i < length (e_body e))%nat ->
  aview rsegs (w_H W2) mem2 (x + Z.of_nat i) = Some (bv_unsigned (nth i (e_body e) NUL))).
{ intros i Hi.
  assert (Hlen : (8 + i < length (Layout.ent_mem e))%nat) by lia.
  pose proof (BE (8 + i)%nat Hlen) as Hb.
  replace (q_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat m) + Z.of_nat (8 + i))
    with (x + Z.of_nat i) in Hb by (unfold x, Layout.OFF_ENT, Layout.ENT_SIZE; lia).
  rewrite Hb. f_equal. f_equal.
  rewrite m2kc_nth_skipn. unfold Layout.ent_mem.
  assert (E8 : forall (a b : Z) (X : list byte), skipn 8 (Cursor.le32 a ++ Cursor.le32 b ++ X) = X)
    by (intros; reflexivity).
  rewrite E8, app_nth1 by exact Hi. reflexivity. }
assert (HAR : AR rsegs B ly2 S2 W2 mem2 md2) by exact (proj1 (proj1 Hcore)).
assert (Hin : In (q_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2)).
{ pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
  destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hppin & _).
  destruct Hcore as (_ & _ & _ & Hperm & _).
  apply (Permutation_in _ (Permutation_sym Hperm)). exact Hppin. }
assert (Hreq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
unfold Layout.PP_SIZE in Hpc, Happ.
pose proof (rtm_blk_ra rsegs B ly2 S2 W2 mem2 md2 (q_pp (x_e rsegs cx)) Layout.PP_SIZE x 46 HAR Hin
  ltac:(unfold x; lia) ltac:(rewrite Hreq; unfold x, Layout.PP_SIZE; lia)) as (Hra & Hhv).
split.
{ split; [|split].
  - intros i Hi. rewrite length_map in Hi.
    replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia.
    rewrite Hbyte by lia. f_equal.
    rewrite (nth_indep _ 0 (bv_unsigned NUL)) by (rewrite length_map; lia). rewrite map_nth.
    f_equal. apply (proj1 (Hci (Z.to_nat i) ltac:(lia))).
  - rewrite length_map, Hbyte by lia. f_equal. exact Hcn.
  - apply Forall_forall. intros b Hb. apply (In_nth _ _ 0) in Hb. destruct Hb as (i & Hi & <-).
    rewrite length_map in Hi.
    rewrite (nth_indep _ 0 (bv_unsigned NUL)) by (rewrite length_map; lia). rewrite map_nth.
    exact (proj2 (Hci i Hi)). }
split; [lia|].
split; [exact Hra|].
split; [exact (Hhv ltac:(lia))|].
unfold amem_range. rewrite C5. unfold x.
unfold kLowShadowBeg in Happ.
destruct Happ as [Ha|Ha]; [left | right]; unfold kHighMemBeg, kHighMemEnd in *; lia.
Qed.

(* ---- the tail: the fresh state at 0x82ad8 after the call (a0 = the wrapper's answer r0, the four spill cells
   hold the five operands, s10 = n_ent and s11 = &ent[0] saved over the call) -> O or KV ---- *)
Lemma m2kc_tail : forall (cx : rs_scx rsegs) POST (at0 m : nat) (fx2 : YK11.FPState) rec kb
ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (r0 : Z),
rs_pre rsegs B cx ->
rs_from_O (fx := fx) rsegs B MT cx POST (S (S m)) ->
m2k_K_val (fx := fx) B MT cx POST rec ->
rs_cut_KM (fx := fx) rsegs B MT cx fx2 rec at0 m kb ly2 S2 W2 regs2 mem2 md2 ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs3 mem3 md3 ->
cs_eq m2kc_L regs2 regs3 ->
getr regs3 (Z_to_bv 5 26) = w64 (Z.of_nat (length (ents rec))) ->
getr regs3 (Z_to_bv 5 27) = w64 (q_pp (x_e rsegs cx) + 0x4014) ->
getr regs3 (Z_to_bv 5 10) = w64 r0 -> -1 <= r0 <= 1 -> (r0 = 0 <-> kb = Rate.RATE_KEY) ->
val_mem rsegs (mrestrict (w_H W2) mem3) (q_R (x_e rsegs cx) + 0x110) 8 (q_pp (x_e rsegs cx) + 0x4018) ->
val_mem rsegs (mrestrict (w_H W2) mem3) (q_R (x_e rsegs cx) + 0x118) 8 (q_pp (x_e rsegs cx) + 0x401c) ->
val_mem rsegs (mrestrict (w_H W2) mem3) (q_R (x_e rsegs cx) + 0x128) 8 (q_pp (x_e rsegs cx) + 0x401c) ->
val_mem rsegs (mrestrict (w_H W2) mem3) (q_R (x_e rsegs cx) + 0x130) 8 (q_pp (x_e rsegs cx) + 0x4014) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ m2k_wz cx a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
SRr rsegs W2 (@cfg_at fx2 rsegs 0x82ad8 regs3 mem3 md3) POST.
Proof using MTL.
intros cx POST at0 m fx2 rec kb ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 r0
  Hpre HO HKV HKM Hcore3 HL H26 H27 H10 Hr0 Hres S110 S118 S128 S130 K3.
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2_stack B cx Hpre) as (HspR & HR16 & Hrsz & Hwin & Hceil & H46 & Hsp47 & Hsp16 & Hev & Hgp & Htp).
pose proof (m2k_apart B cx Hpre) as (Hp0 & Hpc & _ & HF0 & HFc & Hc & _).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in Hceil, Hwin, Hc. unfold Layout.PP_SIZE in Hpc.
pose proof HKM as (Hbase & Hat & Hhz & Hinv & Hrec & Ham & Hm & Hq & Hk).
pose proof Hbase as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1).
pose proof (proj1 Hcore3) as HJ3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof (m2k_nent_le rec Hwf) as Hn32.
assert (HmZ : Z.of_nat m <= 30) by lia.
assert (HatL : rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_chk rsegs cx)).
{ unfold rs_at_cx, rs_at, rs_L_scan in Hat |- *. rewrite !Forall_app in Hat. exact (proj1 (proj1 Hat)). }
unfold rs_at_cx, rs_at, rs_L_scan, rs_L_chk, rs_Hc in Hat. rewrite !Forall_app, !Forall_cons_iff in Hat.
destruct Hat as ((((A8 & A9 & A20 & A18 & AC138 & A21 & AC18 & AC58 & _) &
                   (AC20 & AC38 & AC40 & AC48 & AC50 & AC120 & _)) &
                  (A24 & A27 & A25 & A28 & A19 & A7 & A26 & A31 & A29 & A30 & AC78 & ACc0 & _)) &
                 (A10 & A22 & A23 & _)).
cbn [rt_at rt_xv fst snd] in A8, A9, A20, A18, A21, A24, A27, A25, A28, A19, A7, A26, A31, A29, A30,
  AC78, ACc0, A10, A22, A23.
(* the registers of the state after the call, from the cut's through the kept list *)
assert (A9' : getr regs3 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)))
by (etransitivity; [exact (HL 9%bv ltac:(m2kc_in))|]; exact A9).
assert (A19' : getr regs3 (Z_to_bv 5 19) = w64 (Z.of_nat (length (ents rec)) - 1))
by (etransitivity; [exact (HL 19%bv ltac:(m2kc_in))|]; exact A19).
assert (A22' : getr regs3 (Z_to_bv 5 22) = w64 (Z.of_nat m + 1))
by (etransitivity; [exact (HL 22%bv ltac:(m2kc_in))|]; exact A22).
assert (A23' : getr regs3 (Z_to_bv 5 23) = w64 (Z.of_nat m + 2))
by (etransitivity; [exact (HL 23%bv ltac:(m2kc_in))|]; exact A23).
set (extra := [Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x4018); Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x401c);
               Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x4014)] : list word).
assert (E9 : bv_unsigned (ew (Ereg regs3 extra) 9) = q_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs3 extra 9 (9%bv : bv 5) eq_refl).
  assert (G : getr regs3 9%bv = w64 (q_R (x_e rsegs cx))) by exact A9'.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E10 : ew (Ereg regs3 extra) 10 = Z_to_bv 64 (r0 mod 2 ^ 64)).
{ rewrite (ew_Ereg_nat regs3 extra 10 (10%bv : bv 5) eq_refl).
  assert (G : getr regs3 10%bv = w64 r0) by exact H10.
  rewrite G. symmetry. apply m2_w64_mod. }
assert (E22 : ew (Ereg regs3 extra) 22 = Z_to_bv 64 (Z.of_nat m + 1)).
{ rewrite (ew_Ereg_nat regs3 extra 22 (22%bv : bv 5) eq_refl).
  assert (G : getr regs3 22%bv = w64 (Z.of_nat m + 1)) by exact A22'. exact G. }
assert (E27 : ew (Ereg regs3 extra) 27 = Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x4014)).
{ rewrite (ew_Ereg_nat regs3 extra 27 (27%bv : bv 5) eq_refl).
  assert (G : getr regs3 27%bv = w64 (q_pp (x_e rsegs cx) + 0x4014)) by exact H27. exact G. }
assert (D23 : sv_denot (Ereg regs3 extra) (SOff 23 0) = w64 (Z.of_nat m + 2))
by (rewrite (ck_atom regs3 extra 23 (23%bv : bv 5) eq_refl); exact A23').
assert (D26 : sv_denot (Ereg regs3 extra) (SOff 26 0) = w64 (Z.of_nat (length (ents rec))))
by (rewrite (ck_atom regs3 extra 26 (26%bv : bv 5) eq_refl); exact H26).
assert (D27 : sv_denot (Ereg regs3 extra) (SOff 27 0) = w64 (q_pp (x_e rsegs cx) + 0x4014))
by (rewrite (ck_atom regs3 extra 27 (27%bv : bv 5) eq_refl); exact H27).
assert (D32 : sv_denot (Ereg regs3 extra) (SOff 32 0) = Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x4018))
by (apply (m2k_den_extra regs3 extra 0); [reflexivity | lia]).
assert (D33 : sv_denot (Ereg regs3 extra) (SOff 33 0) = Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x401c))
by (apply (m2k_den_extra regs3 extra 1); [reflexivity | lia]).
assert (D34 : sv_denot (Ereg regs3 extra) (SOff 34 0) = Z_to_bv 64 (q_pp (x_e rsegs cx) + 0x4014))
by (apply (m2k_den_extra regs3 extra 2); [reflexivity | lia]).
pose (rgs := [m2_frame 0x110 0x138 0 0 [YP09.mkChunk 0x110 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x118 (CVal 8 (SOff 33 0));
                                       YP09.mkChunk 0x128 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x130 (CVal 8 (SOff 34 0))]]).
assert (Hrs : Forall (region_ok rsegs (Ereg regs3 extra) (mrestrict (w_H W2) mem3)) rgs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (m2_frame_ok _ W2 mem3 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
  [exact E9 | lia | lia | exact Hpres | lia |].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val rsegs _ _ _ 0x110 8 (SOff 32 0) (q_pp (x_e rsegs cx) + 0x4018)); [exact D32 | cbn; lia | cbn; lia | exact S110].
  - apply (chunk_ok_val rsegs _ _ _ 0x118 8 (SOff 33 0) (q_pp (x_e rsegs cx) + 0x401c)); [exact D33 | cbn; lia | cbn; lia | exact S118].
  - apply (chunk_ok_val rsegs _ _ _ 0x128 8 (SOff 33 0) (q_pp (x_e rsegs cx) + 0x401c)); [exact D33 | cbn; lia | cbn; lia | exact S128].
  - apply (chunk_ok_val rsegs _ _ _ 0x130 8 (SOff 34 0) (q_pp (x_e rsegs cx) + 0x4014)); [exact D34 | cbn; lia | cbn; lia | exact S130]. }
pose proof (m2_entry (fx := fx2) 0x82ad8 [] rgs m2_facts W2 regs3 extra mem3 (Forall_nil _)
  ltac:(vm_compute; reflexivity) Hrs ltac:(cbn; tauto) (m2_facts_ok _ (q_R (x_e rsegs cx)) E9 ltac:(lia) HR16)) as HS.
remember (Ereg regs3 extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 extra) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem3 a)
by (intros; reflexivity).
unfold cfg_at. change (w64 0x82ad8) with (Z_to_bv 64 0x82ad8).
(* 0x82ad8 .. 0x82af8, stop at 0x82afc bnez a0 *)
m2_run m2_awr. ck_keep m2_kwr.
m2_branch Hb.
all: rewrite branch_ne_U, (U_atom E 10 (r0 mod 2 ^ 64) E10 ltac:(apply Z.mod_pos_bound; lia)), U_lit in Hb by lia.
- (* taken: a0 <> 0, the key is not "reac.cfg.rate": back to the outer scan at O with at = m + 2 *)
  apply negb_true_iff in Hb. apply Z.eqb_neq in Hb.
  assert (Hne : kb <> Rate.RATE_KEY).
  { intros Hkq. apply Hb. apply m2kc_mod_zero; [exact Hr0 | apply Hres; exact Hkq]. }
  m2_run_to m2_awr RS_O. ck_keep m2_kwr.
  m2k_rsv HS (7%bv : bv 5) G7.
  m2k_rsv HS (11%bv : bv 5) G11.
  m2k_rsv HS (14%bv : bv 5) G14.
  m2k_rsv HS (26%bv : bv 5) G26.
  m2k_rsv HS (27%bv : bv 5) G27.
  m2k_rsv HS (28%bv : bv 5) G28.
  m2k_rsv HS (29%bv : bv 5) G29.
  m2k_rsv HS (30%bv : bv 5) G30.
  m2k_rsv HS (31%bv : bv 5) G31.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?msn), HAE : env_agree 32 _ ?E,
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msn) ?mdT _,
    KE : forall a, _ -> _ -> aview _ _ (ms_mem ?msn) a = _ |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ m2k_L5 HS HAE ltac:(vm_compute; reflexivity)) as CL5;
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ [19; 24; 25]%bv HS HAE ltac:(vm_compute; reflexivity)) as CO;
    rewrite (st_ok_restrict_mkst rsegs H E ss msn HS eq_refl);
    replace (ss_pc ss) with RS_O by (vm_compute; reflexivity);
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ m2k_wz cx a ->
      aview rsegs (w_H W2) (ms_mem msn) a = aview rsegs (w_H W2) mem2 a)
    by (intros a Ha Hz; rewrite (KE a Ha (fun z => z)); exact (K3 a Ha Hz));
    assert (CL5' : cs_eq m2k_L5 regs2 (ms_regs msn))
    by (apply (cs_eq_trans _ _ regs3); [exact (m2kc_cs_sub _ _ _ _ m2kc_L5_sub HL) | exact CL5]);
    assert (HcoreN : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT)
    by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs3 mem3 md3 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT Hcore3 HJ);
        [ intros r Hr; apply C234; cbv [In];
          destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
        | reflexivity | apply Permutation_refl | m2_io | apply (mo_le_refl MT MTL) |];
        intros a Ha _ _; exact (KE a Ha (fun z => z)));
    destruct (m2k_base_kept (fx := fx) B MT cx fx2 fx2 rec ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT
      Hpre Hbase Hhz HcoreN Hfxk K) as (HbaseN & HhzN);
    apply (HO fx2 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT rec)
  end.
  split; [exact HbaseN|].
  split; [|split; [exact HhzN | split; [|exact Hrec]]].
  + unfold rs_at_cx, rs_at, rs_L_scan. rewrite !Forall_app. split; [split|].
    * eapply (m2k_chk_kept B cx W2 mem2 regs2); [exact Hpre | exact HatL | exact CL5' | exact K].
    * repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
      -- etransitivity; [exact (CO 24%bv ltac:(m2kc_in))|].
         etransitivity; [exact (HL 24%bv ltac:(m2kc_in))|]. exact A24.
      -- etransitivity; [exact G27|]. exact m2kc_m1.
      -- etransitivity; [exact (CO 25%bv ltac:(m2kc_in))|].
         etransitivity; [exact (HL 25%bv ltac:(m2kc_in))|]. exact A25.
      -- etransitivity; [exact G28|]. exact D26.
      -- etransitivity; [exact (CO 19%bv ltac:(m2kc_in))|].
         etransitivity; [exact (HL 19%bv ltac:(m2kc_in))|]. exact A19.
      -- etransitivity; [exact G7|]. exact D27.
      -- etransitivity; [exact G26|]. exact D34.
      -- etransitivity; [exact G31|]. exact D32.
      -- etransitivity; [exact G29|]. exact D33.
      -- etransitivity; [exact G30|]. exact D33.
      -- eapply (m2k_cell_kept B cx W2 mem2 _ _ 0x78); [exact Hpre | lia | lia | lia | exact K | exact AC78].
      -- eapply (m2k_cell_kept B cx W2 mem2 _ _ 0xc0); [exact Hpre | lia | lia | lia | exact K | exact ACc0].
    * repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
      -- replace (Z.of_nat (S (S m))) with (Z.of_nat m + 2) by lia.
         etransitivity; [exact G11|]. exact D23.
      -- exact G14.
  + exact (m2k_inv_mismatch rec at0 m kb Hinv Ham ltac:(lia) Hq Hk Hne).
- (* not taken: a0 = 0, the key is "reac.cfg.rate": a0 := &ent[m + 1] and KV *)
  apply negb_false_iff in Hb. apply Z.eqb_eq in Hb.
  assert (Heq : kb = Rate.RATE_KEY) by (apply Hres; apply m2kc_mod_zero; [exact Hr0 | exact Hb]).
  m2_run_to m2_awr M2K_KV. ck_keep m2_kwr.
  m2k_rsv HS (10%bv : bv 5) G10.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?msn), HAE : env_agree 32 _ ?E,
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msn) ?mdT _,
    KE : forall a, _ -> _ -> aview _ _ (ms_mem ?msn) a = _ |- _ =>
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ m2k_L5 HS HAE ltac:(vm_compute; reflexivity)) as CL5;
    pose proof (cs_eq_of_st_ok _ _ ss msn regs3 _ [24]%bv HS HAE ltac:(vm_compute; reflexivity)) as C24;
    rewrite (st_ok_restrict_mkst rsegs H E ss msn HS eq_refl);
    replace (ss_pc ss) with M2K_KV by (vm_compute; reflexivity);
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ m2k_wz cx a ->
      aview rsegs (w_H W2) (ms_mem msn) a = aview rsegs (w_H W2) mem2 a)
    by (intros a Ha Hz; rewrite (KE a Ha (fun z => z)); exact (K3 a Ha Hz));
    assert (CL5' : cs_eq m2k_L5 regs2 (ms_regs msn))
    by (apply (cs_eq_trans _ _ regs3); [exact (m2kc_cs_sub _ _ _ _ m2kc_L5_sub HL) | exact CL5]);
    assert (G10' : getr (ms_regs msn) (Z_to_bv 5 10)
      = w64 (q_pp (x_e rsegs cx) + 0x4014 + 104 * Z.of_nat (S m)))
    by (etransitivity; [exact G10|];
        rewrite (m2k_denot_a0 E 22 27 (Z.of_nat m + 1) (q_pp (x_e rsegs cx) + 0x4014) E22 ltac:(lia) E27
          ltac:(lia) ltac:(lia));
        unfold w64; f_equal; lia);
    assert (HcoreN : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT)
    by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs3 mem3 md3 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT Hcore3 HJ);
        [ intros r Hr; apply C234; cbv [In];
          destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
        | reflexivity | apply Permutation_refl | m2_io | apply (mo_le_refl MT MTL) |];
        intros a Ha _ _; exact (KE a Ha (fun z => z)));
    destruct (m2k_base_kept (fx := fx) B MT cx fx2 fx2 rec ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT
      Hpre Hbase Hhz HcoreN Hfxk K) as (HbaseN & HhzN);
    apply (HKV fx2 ly2 S2 W2 (ms_regs msn) (ms_mem msn) mdT (nth (S m) (ents rec) m2k_d)
      (q_pp (x_e rsegs cx) + 0x4014 + 104 * Z.of_nat (S m)) HbaseN HhzN)
  end.
  + unfold rs_at_cx, rs_at. rewrite Forall_app. split.
    * eapply (m2k_chk_kept B cx W2 mem2 regs2); [exact Hpre | exact HatL | exact CL5' | exact K].
    * repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
      -- etransitivity; [exact (C24 24%bv ltac:(m2kc_in))|].
         etransitivity; [exact (HL 24%bv ltac:(m2kc_in))|]. exact A24.
      -- exact G10'.
      -- eapply (m2k_cell_kept B cx W2 mem2 _ _ 0x78); [exact Hpre | lia | lia | lia | exact K | exact AC78].
      -- eapply (m2k_cell_kept B cx W2 mem2 _ _ 0xc0); [exact Hpre | lia | lia | lia | exact K | exact ACc0].
  + eapply (m2k_ent_at (fx := fx) B MT cx fx2 rec ly2 S2 W2); [exact Hpre | exact HbaseN | lia].
  + split; [exact (m2k_inv_match rec at0 m kb Hinv Ham ltac:(lia) Hq Hk Heq)|].
    destruct Hrec as (_ & _ & _ & Hsnd & Hfst). split; [exact Hsnd | exact Hfst].
Qed.

(* ---- KM 0x82aac: a1 := m; the dead `blt a1,s11` (s11 = -1, m >= 0, decided by s6's fact); a1 := the key
   literal 0x20fa0; the four spills; jal the strcmp wrapper 0x4219c, ra = 0x82ad8 ---- *)
Lemma m2k_key : m2k_key_stmt B MT.
Proof using MTL ASTRCMP.
unfold m2k_key_stmt, rs_from_KM.
intros cx POST inp at0 m Hst HO HKV fx2 ly2 S2 W2 regs2 mem2 md2 rec kb HKM.
pose proof Hst as (Hpre & _).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2_stack B cx Hpre) as (HspR & HR16 & Hrsz & Hwin & Hceil & H46 & Hsp47 & Hsp16 & Hev & Hgp & Htp).
pose proof (m2k_apart B cx Hpre) as (Hp0 & Hpc & Happ & HF0 & HFc & Hc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_SEG_STK, ASTACK in Hceil, Hwin, Hc. unfold Layout.PP_SIZE in Hpc.
pose proof HKM as (Hbase & Hat & Hhz & Hinv & Hrec & Ham & Hm & Hq & Hk).
pose proof Hbase as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1).
pose proof (m2k_nent_le rec Hwf) as Hn32.
assert (HmZ : Z.of_nat m <= 30) by lia.
pose proof (proj1 Hcore) as HJ0.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
clear HJ0.
unfold rs_at_cx, rs_at, rs_L_scan, rs_L_chk, rs_Hc in Hat. rewrite !Forall_app, !Forall_cons_iff in Hat.
destruct Hat as ((((A8 & A9 & A20 & A18 & AC138 & A21 & AC18 & AC58 & _) &
                   (AC20 & AC38 & AC40 & AC48 & AC50 & AC120 & _)) &
                  (A24 & A27 & A25 & A28 & A19 & A7 & A26 & A31 & A29 & A30 & AC78 & ACc0 & _)) &
                 (A10 & A22 & A23 & _)).
cbn [rt_at rt_xv fst snd] in A8, A9, A20, A18, A21, A24, A27, A25, A28, A19, A7, A26, A31, A29, A30,
  AC78, ACc0, A10, A22, A23.
assert (Hsp : spZ regs2 = q_R (x_e rsegs cx)).
{ rewrite <- HspR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
set (x := q_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m).
assert (E9 : bv_unsigned (ew (Ereg regs2 []) 9) = q_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs2 [] 9 (9%bv : bv 5) eq_refl).
  assert (G : getr regs2 9%bv = w64 (q_R (x_e rsegs cx))) by exact A9.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E22 : bv_unsigned (ew (Ereg regs2 []) 22) = Z.of_nat m + 1).
{ rewrite (ew_Ereg_nat regs2 [] 22 (22%bv : bv 5) eq_refl).
  assert (G : getr regs2 22%bv = w64 (Z.of_nat m + 1)) by exact A22.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (D10 : sv_denot (Ereg regs2 []) (SOff 10 0) = w64 x)
by (rewrite (ck_atom regs2 [] 10 (10%bv : bv 5) eq_refl); exact A10).
assert (D26 : sv_denot (Ereg regs2 []) (SOff 26 0) = w64 (q_pp (x_e rsegs cx) + 0x4014))
by (rewrite (ck_atom regs2 [] 26 (26%bv : bv 5) eq_refl); exact A26).
assert (D29 : sv_denot (Ereg regs2 []) (SOff 29 0) = w64 (q_pp (x_e rsegs cx) + 0x401c))
by (rewrite (ck_atom regs2 [] 29 (29%bv : bv 5) eq_refl); exact A29).
assert (D30 : sv_denot (Ereg regs2 []) (SOff 30 0) = w64 (q_pp (x_e rsegs cx) + 0x401c))
by (rewrite (ck_atom regs2 [] 30 (30%bv : bv 5) eq_refl); exact A30).
assert (D31 : sv_denot (Ereg regs2 []) (SOff 31 0) = w64 (q_pp (x_e rsegs cx) + 0x4018))
by (rewrite (ck_atom regs2 [] 31 (31%bv : bv 5) eq_refl); exact A31).
assert (D28 : sv_denot (Ereg regs2 []) (SOff 28 0) = w64 (Z.of_nat (length (ents rec))))
by (rewrite (ck_atom regs2 [] 28 (28%bv : bv 5) eq_refl); exact A28).
assert (D7 : sv_denot (Ereg regs2 []) (SOff 7 0) = w64 (q_pp (x_e rsegs cx) + 0x4014))
by (rewrite (ck_atom regs2 [] 7 (7%bv : bv 5) eq_refl); exact A7).
pose (rgs := [m2_frame 0x110 0x120 0x110 0x120 []; m2_frame 0x128 0x138 0x128 0x138 []]).
assert (Hrs : Forall (region_ok rsegs (Ereg regs2 []) (mrestrict (w_H W2) mem2)) rgs).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (m2_frame_ok _ W2 mem2 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres | lia | apply Forall_nil].
  - apply (m2_frame_ok _ W2 mem2 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres | lia | apply Forall_nil]. }
assert (Hpd : pairwise_disjoint (Ereg regs2 []) rgs).
{ unfold rgs, m2_frame. cbn [pairwise_disjoint all_disjoint].
  split; [split; [|exact I] | split; exact I].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9. left. lia. }
pose proof (m2_entry (fx := fx2) RS_KM [(27%bv, SLit (-1))] rgs m2kc_facts W2 regs2 [] mem2) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
  [ intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
  | symmetry; exact A27 ])
  ltac:(vm_compute; reflexivity) Hrs Hpd
  (m2kc_facts_ok _ (q_R (x_e rsegs cx)) (Z.of_nat m + 1) E9 ltac:(lia) HR16 E22 ltac:(lia))).
remember (Ereg regs2 []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((q_R (x_e rsegs cx) + 0x110 <= a < q_R (x_e rsegs cx) + 0x120) \/
     (q_R (x_e rsegs cx) + 0x128 <= a < q_R (x_e rsegs cx) + 0x138)) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
pose proof (proj1 Hcore) as HJ.
unfold cfg_at. change (w64 RS_KM) with (Z_to_bv 64 RS_KM).
(* 0x82aac .. 0x82ad4, stop at the wrapper's entry 0x4219c *)
m2_run m2_awr. ck_keep m2_kwr.
m2k_rsv HS (1%bv : bv 5) G1.
m2k_rsv HS (10%bv : bv 5) G10.
m2k_rsv HS (11%bv : bv 5) G11.
m2k_rsv HS (26%bv : bv 5) G26c.
m2k_rsv HS (27%bv : bv 5) G27c.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82ad8) by exact G1.
assert (R10' : getr (ms_regs ms) 10 = w64 x) by (etransitivity; [exact G10|]; exact D10).
assert (R11' : getr (ms_regs ms) 11 = w64 M2_KEY) by exact G11.
(* the four spill cells of the state after the run *)
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
  assert (HR0 : region_ok rsegs E (mrestrict H (ms_mem ms))
    (YP09.mkRegion (Some 9%nat) 0x110 0x120 0x110 0x120
       [YP09.mkChunk 0x110 (CVal 8 (SOff 31 0)); YP09.mkChunk 0x118 (CVal 8 (SOff 30 0))]))
  by (apply (m2kc_region_nth H E ss ms 0); [exact HS | vm_compute; reflexivity]);
  assert (HR1 : region_ok rsegs E (mrestrict H (ms_mem ms))
    (YP09.mkRegion (Some 9%nat) 0x128 0x138 0x128 0x138
       [YP09.mkChunk 0x128 (CVal 8 (SOff 29 0)); YP09.mkChunk 0x130 (CVal 8 (SOff 26 0))]))
  by (apply (m2kc_region_nth H E ss ms 1); [exact HS | vm_compute; reflexivity])
end.
assert (E9' : bv_unsigned (ew E 9) = q_R (x_e rsegs cx)) by (subst E; exact E9).
assert (T110 : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (q_R (x_e rsegs cx) + 0x110) 8
  (q_pp (x_e rsegs cx) + 0x4018)).
{ pose proof (m2kc_field E _ 9%nat (q_R (x_e rsegs cx)) _ 0x110 0x120 0x110 0x120 0x110 8 (SOff 31 0)
    (q_pp (x_e rsegs cx) + 0x4018) HR0 E9' ltac:(cbn; tauto) D31 ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  change (N.to_nat 8) with 8%nat in Hv. exact Hv. }
assert (T118 : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (q_R (x_e rsegs cx) + 0x118) 8
  (q_pp (x_e rsegs cx) + 0x401c)).
{ pose proof (m2kc_field E _ 9%nat (q_R (x_e rsegs cx)) _ 0x110 0x120 0x110 0x120 0x118 8 (SOff 30 0)
    (q_pp (x_e rsegs cx) + 0x401c) HR0 E9' ltac:(cbn; tauto) D30 ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  change (N.to_nat 8) with 8%nat in Hv. exact Hv. }
assert (T128 : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (q_R (x_e rsegs cx) + 0x128) 8
  (q_pp (x_e rsegs cx) + 0x401c)).
{ pose proof (m2kc_field E _ 9%nat (q_R (x_e rsegs cx)) _ 0x128 0x138 0x128 0x138 0x128 8 (SOff 29 0)
    (q_pp (x_e rsegs cx) + 0x401c) HR1 E9' ltac:(cbn; tauto) D29 ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  change (N.to_nat 8) with 8%nat in Hv. exact Hv. }
assert (T130 : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (q_R (x_e rsegs cx) + 0x130) 8
  (q_pp (x_e rsegs cx) + 0x4014)).
{ pose proof (m2kc_field E _ 9%nat (q_R (x_e rsegs cx)) _ 0x128 0x138 0x128 0x138 0x130 8 (SOff 26 0)
    (q_pp (x_e rsegs cx) + 0x4014) HR1 E9' ltac:(cbn; tauto) D26 ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  change (N.to_nat 8) with 8%nat in Hv. exact Hv. }
(* the registers of the call state, and the kept bytes *)
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ m2kc_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with M2_STRCMP by (vm_compute; reflexivity)
end.
assert (HspT : spZ (ms_regs ms) = q_R (x_e rsegs cx))
by (rewrite (m2_sp_of_cs [2; 3; 4]%bv _ _ ltac:(cbv [In]; left; reflexivity) C234); exact Hsp).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ m2k_wz cx a ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hz. apply (KE a Ha). intros Hcc. apply Hz. unfold m2k_wz. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdT) _ =>
assert (HcoreT : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore
      ltac:(eassumption));
    [ intros r Hr; apply C234; cbv [In];
      destruct Hr as [->|[->| ->]]; repeat (first [left; apply bv_eq; reflexivity | right])
    | reflexivity | apply Permutation_refl | m2_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ He; apply (KE a Ha); intros Hcc; exact (He (m2kc_spill_E2 cx a Hcc)))
end.
destruct (m2k_base_kept (fx := fx) B MT cx fx2 fx2 rec ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _
  Hpre Hbase Hhz HcoreT Hfxk KT) as (HbaseT & HhzT).
destruct (m2kc_key_str cx fx2 rec ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ m kb Hpre HbaseT ltac:(lia) Hk)
  as (Hcx & Hxlen & Hrx46 & Hhx46 & Hmx46).
fold x in Hcx, Hrx46, Hhx46, Hmx46.
assert (HyT : rt_cstr rsegs (w_H W2) (ms_mem ms) M2_KEY (map (fun b : byte => bv_unsigned b) Rate.RATE_KEY))
  by exact (m2_key_at B MT cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT).
assert (Hklen : Z.of_nat (length (map (fun b : byte => bv_unsigned b) Rate.RATE_KEY)) = 13)
  by (vm_compute; reflexivity).
assert (Hxl : Z.of_nat (length (map (fun b : byte => bv_unsigned b) kb)) < 45)
  by (rewrite length_map; lia).
destruct (str_meet_of_cstr rsegs (map (fun b : byte => bv_unsigned b) kb) W2 (ms_mem ms) x
  (map (fun b : byte => bv_unsigned b) Rate.RATE_KEY) M2_KEY Hcx
  (cstr_at_of_rt_cstr rsegs W2 (ms_mem ms) M2_KEY _ HyT))
as (kk & c1 & c2 & Hmeet & Hk1 & Hk2 & Hres0).
assert (Hres : strcmp_res c1 c2 = 0 <-> kb = Rate.RATE_KEY).
{ split; intros H.
  - apply m2k_map_bv_inj. apply Hres0. exact H.
  - apply Hres0. rewrite H. reflexivity. }
(* the wrapper's premises on the two strings *)
assert (Hx0 : 0 < x) by (unfold x; lia).
assert (Hxhi : x + 46 <= alloc_ceiling) by (unfold x; lia).
destruct (rt_cstr_args rsegs W2 (ms_regs ms) (ms_mem ms) M2_KEY
  (map (fun b : byte => bv_unsigned b) Rate.RATE_KEY) kk HyT ltac:(lia)
  ltac:(intros b Hb; rewrite HspT; unfold M2_KEY, ESTACK in *; lia))
as (Hy0 & Hyk & Hsy & Hmy & Hry & Hhy).
assert (Hsx : src_ok rsegs W2 (ms_regs ms) (ms_mem ms) x (kk + 1)).
{ intros a Ha. destruct Hcx as (Hc1 & Hc2 & _). split.
  - destruct (Z.eq_dec (a - x) (Z.of_nat (length (map (fun b : byte => bv_unsigned b) kb)))) as [He|He].
    + replace a with (x + Z.of_nat (length (map (fun b : byte => bv_unsigned b) kb))) by lia.
      rewrite Hc2. discriminate.
    + replace a with (x + (a - x)) by lia. rewrite (Hc1 (a - x) ltac:(lia)). discriminate.
  - rewrite HspT. unfold ESTACK. lia. }
eapply SRr_bind.
{ eapply (aj_strcmp_at rsegs B LAWS ck_segs_low M2_STRCMP (ASTRCMP fx2) W2 (ms_regs ms) (ms_mem ms)
    (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 _ (x_k rsegs cx)
    x M2_KEY kk c1 c2 (q_R (x_e rsegs cx) - x_sp0 rsegs cx) (w64 0x82ad8)
    ltac:(eassumption) R10' R11' Hx0 Hy0 ltac:(lia) ltac:(lia) ltac:(lia) Hmeet
    ltac:(rewrite HspT; lia));
  [ (* o mod 16 = 0 *)
    replace (q_R (x_e rsegs cx) - x_sp0 rsegs cx)
      with (q_R (x_e rsegs cx) + (-1) * x_sp0 rsegs cx) by lia;
    rewrite Zplus_mod, Zmult_mod, HR16, Hsp16; reflexivity
  | lia
  | unfold ESTACK; lia
  | (* gp *) etransitivity; [exact (CL 3%bv ltac:(m2kc_in))|];
    etransitivity; [exact ((proj1 (proj2 Hcore)) 3 ltac:(lia))|]; exact Hgp
  | (* tp *) etransitivity; [exact (CL 4%bv ltac:(m2kc_in))|];
    etransitivity; [exact ((proj1 (proj2 Hcore)) 4 ltac:(lia))|]; exact Htp
  | exact R1'
  | vm_compute; reflexivity
  | exact Hsx | exact Hsy
  | intros a Ha; unfold ESTACK; lia
  | intros a Ha; unfold M2_KEY, ESTACK in *; lia
  | exact (amem_range_sub x 46 (kk + 1) ltac:(lia) Hmx46)
  | exact Hmy
  | exact (range_addressable_sub _ _ x 46 (kk + 1) ltac:(lia) Hrx46)
  | exact (shadow_hull_vis_sub _ x 46 (kk + 1) ltac:(lia) Hhx46)
  | exact Hry | exact Hhy ]. }
cbv beta. intros W' c' _ (-> & regsR & memR & mdR & -> & HJR & HPR & Hsame & HR10 & HK2 & _).
(* the state at 0x82ad8: a0 = the wrapper's answer, the callee-saved registers and the spills as at the call *)
assert (HcoreR : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regsR memR mdR).
{ apply (m2_core_step B MT MTL cx _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ ly2 S2 W2 regsR memR mdR HcoreT HJR);
  [ intros r Hr; apply HPR; unfold acallee_saved; lia
  | reflexivity | apply Permutation_refl | exact Hsame | apply (mo_le_refl MT MTL) |].
  intros a Ha Hs _. apply HK2; [exact Ha|].
  rewrite HspR in Hs. unfold T_SEG_STK, ASTACK in Hs. unfold ESTACK. lia. }
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ m2k_wz cx a ->
  aview rsegs (w_H W2) memR a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hz. rewrite (HK2 a Ha ltac:(unfold m2k_wz, T_SEG_STK, ASTACK, ESTACK in *; lia)).
  exact (KT a Ha Hz). }
assert (HLR : cs_eq m2kc_L regs2 regsR).
{ apply (cs_eq_trans _ _ (ms_regs ms)); [exact CL|].
  exact (cs_eq_of_pres m2kc_L _ _ m2kc_L_cs HPR). }
apply (m2kc_tail cx POST at0 m fx2 rec kb ly2 S2 W2 regs2 mem2 md2 regsR memR mdR (strcmp_res c1 c2)
  Hpre HO (HKV rec) HKM HcoreR HLR).
- (* s10 = n_ent, saved over the call *)
  etransitivity; [exact (HPR 26 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact G26c|]. exact D28.
- (* s11 = &ent[0], saved over the call *)
  etransitivity; [exact (HPR 27 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact G27c|]. exact D7.
- exact HR10.
- exact (m2kc_res_range c1 c2).
- exact Hres.
- eapply (val_mem_kept rsegs); [|exact T110]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  apply HK2; [lia|]. unfold ESTACK. lia.
- eapply (val_mem_kept rsegs); [|exact T118]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  apply HK2; [lia|]. unfold ESTACK. lia.
- eapply (val_mem_kept rsegs); [|exact T128]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  apply HK2; [lia|]. unfold ESTACK. lia.
- eapply (val_mem_kept rsegs); [|exact T130]. intros j Hj. change (Z.of_nat 8) with 8 in Hj.
  apply HK2; [lia|]. unfold ESTACK. lia.
- exact KR.
Qed.
(* ===================================== the piece ===================================== *)
(* KM -> O (mismatch, at = m + 2) | KV -> FLT / MAL / JN -> A, by m2k_chain *)
Theorem rt_m02_key_A : rs_piece_W11b_key_stmt rsegs B MT.
Proof using MTL HGOT HSC ASTRCMP.
exact (m2k_chain B MT (m2k_join B MT MTL) m2k_float (m2k_val B MT MTL) m2k_key).
Qed.
End t.

Print Assumptions rt_m02_key_A.
