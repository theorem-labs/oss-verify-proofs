(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its addresses changed; 1951 of its 2084 lines of code are new or changed and 1010 lines of the source are left out. *)
(* Segment D3 of LLVMFuzzerTestOneInput's ASan walk: the REAC-version case of the record switch,
   0x80f20 .. the join 0x813b4. seg_D3 of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v: from inv_caseV to inv_tail.

   The code (BASE + 0x814 .. BASE + 0xa60, then j 0x813b4):
     0x80f20..0x80fd0  the three halfword checks id.major/minor/patch = pl[2..3], pl[4..5], pl[6..7] (big-endian),
                       each byte read after its shadow check (the payload copy pl is a heap block of k >= 8 bytes)
     0x80fd4..0x80fec  the shadow of `v` (SF+224, 20 bytes) and `ev` (SF+288, 24 bytes) unpoisoned
     0x80ff0..0x81058  en = 0; put_dec(ev, &en, major, 1); ev[en++] = '.'; put_dec(ev, &en, minor, 1);
                       put_dec(ev, &en, patch, 2)   (en lives at mf+208, put_dec's p)
     0x8105c..0x81094  ev[en] = 0; reac_identity_reac_ver_str(major, minor, patch, v, 20)
     0x81098..0x810b8  w >= 0, w = en, bcmp(v, ev, en + 1) (the bcmp interceptor)
     0x810bc..0x81148  hw.have = 1 and hw.hw = pl[0..8) (two checked reads of pl's shadow, two word stores)
     0x8114c..0x8116c  `v` and `ev` re-poisoned (0xf8), x21 := i from mf+160, j 0x813b4
   Every abort branch is decided by a fact: the halfword checks and the version string from the plain model
   (lib/Prog/SlotModel.v, RcIdentModel.v: an accepted version record writes be16 pl[2..3] etc. to the identity),
   the string compare by the bcmp interceptor's post. The walk runs on the boundary's own journal (own = the
   entry's class-4 frame), so put_dec and reac_identity_reac_ver_str, which write `ev`, `v` and mf+208, take it
   directly in their caller-journal form. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YN0d YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv put_dec write_uint reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec put_dec_c
  write_uint_c reac_identity_reac_ver_str_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off for every file that loads it; the address arithmetic of
   this segment (shadow_addr, the frame's alignment) needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model's facts the segment reads (lib/Prog/SlotModel.v, RcIdentModel.v, IdentSpec.v) ---------- *)
Module D3M.
Import SlotModel RcIdentModel.
Lemma bz_zb_mod : forall z, bz (zb z) = z mod 256.
Proof.
intros z. unfold bz, zb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. reflexivity.
Qed.
(* An accepted version record: the three halfwords of the new identity are pl[2..3], pl[4..5], pl[6..7]. *)
Lemma ver_fields : forall idb p, length idb = ID_SIZE -> (8 <= length p)%nat ->
  major (snd (ING idb ADDR_REAC_VERSION p)) = bz (nthb p 2) * 256 + bz (nthb p 3) /\
  minor (snd (ING idb ADDR_REAC_VERSION p)) = bz (nthb p 4) * 256 + bz (nthb p 5) /\
  patch (snd (ING idb ADDR_REAC_VERSION p)) = bz (nthb p 6) * 256 + bz (nthb p 7).
Proof.
intros idb p Hl Hp. rewrite ING_ver_dispatch. unfold ing_version.
destruct (Nat.leb_spec REAC_VER_LEN (length p)) as [E|E]; [|unfold REAC_VER_LEN in E; lia]. cbn [snd].
pose proof (bz_range (nthb p 2)) as R2. pose proof (bz_range (nthb p 3)) as R3.
pose proof (bz_range (nthb p 4)) as R4. pose proof (bz_range (nthb p 5)) as R5.
pose proof (bz_range (nthb p 6)) as R6. pose proof (bz_range (nthb p 7)) as R7.
unfold major, minor, patch, nthb in *. unfold OFF_RAW, OFF_MAJOR, OFF_MINOR, OFF_PATCH, OFF_HAS_VER, REAC_VER_LEN.
rewrite (nth_upd_before _ _ 36 22), (nth_upd_before _ _ 26 22), (nth_upd_before _ _ 24 22), (nth_upd_in _ _ 22 22) by lsolve.
rewrite (nth_upd_before _ _ 36 23), (nth_upd_before _ _ 26 23), (nth_upd_before _ _ 24 23), (nth_upd_in _ _ 22 23) by lsolve.
rewrite (nth_upd_before _ _ 36 24), (nth_upd_before _ _ 26 24), (nth_upd_in _ _ 24 24) by lsolve.
rewrite (nth_upd_before _ _ 36 25), (nth_upd_before _ _ 26 25), (nth_upd_in _ _ 24 25) by lsolve.
rewrite (nth_upd_before _ _ 36 26), (nth_upd_in _ _ 26 26) by lsolve.
rewrite (nth_upd_before _ _ 36 27), (nth_upd_in _ _ 26 27) by lsolve.
cbn [Nat.sub nth le16]. rewrite !bz_zb_mod. unfold be16.
set (a2 := bz (nth 2 p (zb 0))) in *. set (a3 := bz (nth 3 p (zb 0))) in *. set (a4 := bz (nth 4 p (zb 0))) in *.
set (a5 := bz (nth 5 p (zb 0))) in *. set (a6 := bz (nth 6 p (zb 0))) in *. set (a7 := bz (nth 7 p (zb 0))) in *.
split; [|split]; Z.div_mod_to_equations; lia.
Qed.
Lemma ver_k8 : forall inp i, rec_r inp i = 1 -> rec_addr inp i = ADDR_REAC_VERSION -> 8 <= rec_k inp i.
Proof.
intros inp i Hr Ha. pose proof (rec_pl_length inp i) as Hk. pose proof (rec_k_range inp i) as Hkr.
unfold rec_r in Hr. rewrite Ha in Hr.
destruct (Nat.leb_spec 8 (length (rec_pl inp i))) as [L|L]; [lia|].
rewrite ING_ver_short in Hr by exact L. cbn [fst] in Hr. discriminate Hr.
Qed.
Lemma ver_id : forall inp i, rec_r inp i = 1 -> rec_addr inp i = ADDR_REAC_VERSION ->
  major (rec_id inp (S i)) = bz (nthb (rec_pl inp i) 2) * 256 + bz (nthb (rec_pl inp i) 3) /\
  minor (rec_id inp (S i)) = bz (nthb (rec_pl inp i) 4) * 256 + bz (nthb (rec_pl inp i) 5) /\
  patch (rec_id inp (S i)) = bz (nthb (rec_pl inp i) 6) * 256 + bz (nthb (rec_pl inp i) 7).
Proof.
intros inp i Hr Ha. pose proof (ver_k8 inp i Hr Ha) as H8. pose proof (rec_pl_length inp i) as Hk.
cbn [rec_id]. rewrite Ha. apply ver_fields; [apply rec_id_length | lia].
Qed.
Lemma ver_hw : forall inp i, rec_r inp i = 1 -> rec_addr inp i = ADDR_REAC_VERSION ->
  rec_have inp (S i) = 1 /\ rec_hwb inp (S i) = firstn 8 (rec_pl inp i).
Proof.
intros inp i Hr Ha. pose proof (ver_k8 inp i Hr Ha) as H8.
unfold rec_have, rec_hwb. cbn [rec_hw]. rewrite Ha, Z.eqb_refl.
rewrite (proj2 (Z.leb_le 8 (rec_k inp i)) H8). cbn [andb]. split; reflexivity.
Qed.
Lemma mmp_range : forall idb, 0 <= major idb < 65536 /\ 0 <= minor idb < 65536 /\ 0 <= patch idb < 65536.
Proof.
intros idb. unfold major, minor, patch.
pose proof (bz_range (nthb idb 22)). pose proof (bz_range (nthb idb 23)).
pose proof (bz_range (nthb idb 24)). pose proof (bz_range (nthb idb 25)).
pose proof (bz_range (nthb idb 26)). pose proof (bz_range (nthb idb 27)). lia.
Qed.
End D3M.

(* put_dec's digits are write_uint's (IdentSpec.DEC against write_uint_c / reac_identity_reac_ver_str_c), checked
   for every 16-bit value at once. *)
Lemma d3_dec_all : IdentSpec.z_all (fun v =>
  IdentSpec.bytes_eqb (IdentSpec.DEC v 1) (write_uint_c.write_uint_D v) &&
  IdentSpec.bytes_eqb (IdentSpec.DEC v 2) (reac_identity_reac_ver_str_c.reac_ver_str_DEC2 v)) (Z.to_nat 65536) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma d3_DEC : forall v, 0 <= v < 65536 ->
  IdentSpec.DEC v 1 = write_uint_c.write_uint_D v /\
  IdentSpec.DEC v 2 = reac_identity_reac_ver_str_c.reac_ver_str_DEC2 v.
Proof.
intros v Hv. pose proof (IdentSpec.z_all_spec _ _ _ d3_dec_all v ltac:(rewrite Z2Nat.id by lia; lia)) as H.
cbv beta in H. apply andb_true_iff in H as [H1 H2]. split; apply IdentSpec.bytes_eqb_eq; assumption.
Qed.
(* The expected string ev and its length: what reac_identity_reac_ver_str writes. *)
Definition d3_EV (ma mi pa : Z) : list byte :=
  IdentSpec.DEC ma 1 ++ [Z_to_bv 8 46] ++ IdentSpec.DEC mi 1 ++ IdentSpec.DEC pa 2.
Lemma d3_EV_VER : forall ma mi pa, 0 <= ma < 65536 -> 0 <= mi < 65536 -> 0 <= pa < 65536 ->
  d3_EV ma mi pa = reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa.
Proof.
intros ma mi pa H1 H2 H3. unfold d3_EV, reac_identity_reac_ver_str_c.reac_ver_str_VER.
rewrite (proj1 (d3_DEC ma H1)), (proj1 (d3_DEC mi H2)), (proj2 (d3_DEC pa H3)). reflexivity.
Qed.
Lemma d3_dl1 : forall v, 0 <= v < 65536 -> 1 <= put_dec_c.dec_len v 1 <= 5.
Proof.
intros v Hv. unfold put_dec_c.dec_len. rewrite (proj1 (d3_DEC v Hv)).
exact (rvs_n_range v).
Qed.
Lemma d3_dl2 : forall v, 0 <= v < 65536 -> 2 <= put_dec_c.dec_len v 2 <= 5.
Proof.
intros v Hv. unfold put_dec_c.dec_len. rewrite (proj2 (d3_DEC v Hv)).
unfold reac_identity_reac_ver_str_c.reac_ver_str_DEC2.
destruct (Z.ltb_spec v 10) as [L|L]; [cbn; lia|].
pose proof (rvs_n_range v) as R. pose proof (rvs_n_ge10 v L) as G. unfold rvs_n, write_uint_c.write_uint_n in *. lia.
Qed.
Lemma d3_LV : forall ma mi pa, 0 <= ma < 65536 -> 0 <= mi < 65536 -> 0 <= pa < 65536 ->
  put_dec_c.dec_len ma 1 + 1 + put_dec_c.dec_len mi 1 + put_dec_c.dec_len pa 2 = rvs_LV ma mi pa.
Proof.
intros ma mi pa H1 H2 H3. unfold rvs_LV, reac_identity_reac_ver_str_c.reac_ver_str_LV.
rewrite <- (d3_EV_VER ma mi pa H1 H2 H3). unfold d3_EV, put_dec_c.dec_len.
rewrite !length_app. cbn [length]. lia.
Qed.

(* ---- arithmetic of the symbolic values ---------------------------------------------------------------------- *)
Lemma d3_lor_shl : forall x y k, 0 <= k -> 0 <= x -> 0 <= y < 2 ^ k -> Z.lor (Z.shiftl x k) y = x * 2 ^ k + y.
Proof.
intros x y k Hk Hx Hy.
assert (L : Z.land (Z.shiftl x k) y = 0).
{ apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases j k).
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec y 0) as [->|Hy0]; [rewrite Z.bits_0; apply andb_false_r|].
    assert (Lg : Z.log2 y < k) by (apply Z.log2_lt_pow2; lia).
    rewrite (Z.bits_above_log2 y j) by lia. apply andb_false_r. }
rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L.
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma d3_U_be16 : forall E n1 n2 v1 v2, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
  0 <= v1 < 256 -> 0 <= v2 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n2 0)) = v1 * 256 + v2.
Proof.
intros E n1 n2 v1 v2 H1 H2 R1 R2.
rewrite U_SAlu, U_SAlu, (U_atom E n1 v1 H1 ltac:(lia)), (U_atom E n2 v2 H2 ltac:(lia)), U_SLit.
cbn [zalu_raw]. change (Z.land (zcanon 8) 63) with 8.
rewrite (zcanon_id (Z.shiftl v1 8)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
rewrite (d3_lor_shl v1 v2 8) by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* hw.hw's two words (0x810f4 .. 0x81140): four bytes or-ed little-endian. *)
Lemma d3_U_le32 : forall E n0 n1 n2 n3 b0 b1 b2 b3,
  ew E n0 = Z_to_bv 64 b0 -> ew E n1 = Z_to_bv 64 b1 -> ew E n2 = Z_to_bv 64 b2 -> ew E n3 = Z_to_bv 64 b3 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff n3 0) (SLit 24)) (SAlu ALU_SLL (SOff n2 0) (SLit 16)))
                   (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n0 0)))
  = b0 + 256 * b1 + 65536 * b2 + 16777216 * b3.
Proof.
intros E n0 n1 n2 n3 b0 b1 b2 b3 H0 H1 H2 H3 R0 R1 R2 R3.
rewrite !U_SAlu. rewrite (U_atom E n0 b0 H0 ltac:(lia)), (U_atom E n1 b1 H1 ltac:(lia)), (U_atom E n2 b2 H2 ltac:(lia)),
  (U_atom E n3 b3 H3 ltac:(lia)), !U_SLit.
cbn [zalu_raw].
change (Z.land (zcanon 8) 63) with 8. change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 24) 63) with 24.
rewrite (zcanon_id (Z.shiftl b1 8)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
rewrite (zcanon_id (Z.shiftl b2 16)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
rewrite (zcanon_id (Z.shiftl b3 24)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
rewrite (d3_lor_shl b1 b0 8) by lia. rewrite (zcanon_id (b1 * 2 ^ 8 + b0)) by (unfold M64; lia).
assert (E3 : Z.lor (Z.shiftl b3 24) (Z.shiftl b2 16) = Z.shiftl (b3 * 2 ^ 8 + b2) 16).
{ replace (Z.shiftl b3 24) with (Z.shiftl (Z.shiftl b3 8) 16) by (rewrite Z.shiftl_shiftl by lia; reflexivity).
  rewrite <- Z.shiftl_lor. rewrite (d3_lor_shl b3 b2 8) by lia. reflexivity. }
rewrite E3. rewrite (zcanon_id (Z.shiftl (b3 * 2 ^ 8 + b2) 16)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
rewrite (d3_lor_shl (b3 * 2 ^ 8 + b2) (b1 * 2 ^ 8 + b0) 16) by lia.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* The abort side of each halfword check (0x80f4c, 0x80f8c, 0x80fcc) is impossible. *)
Lemma d3_be16_taken : forall E n1 n2 nr v1 v2, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
  ew E nr = Z_to_bv 64 (v1 * 256 + v2) -> 0 <= v1 < 256 -> 0 <= v2 < 256 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n2 0))) (sv_denot E (SOff nr 0))
  = true.
Proof.
intros E n1 n2 nr v1 v2 H1 H2 Hr R1 R2. rewrite branch_eq_U, (d3_U_be16 E n1 n2 v1 v2 H1 H2 R1 R2).
rewrite (U_atom E nr (v1 * 256 + v2) Hr ltac:(lia)). apply Z.eqb_refl.
Qed.
Lemma d3_Z_to_bv_mod64 : forall t, Z_to_bv 64 (t mod 2 ^ 64) = Z_to_bv 64 t.
Proof.
intros t. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

(* ---- the symbolic state at 0x80f20 ------------------------------------------------------------------------- *)
(* Atoms: the registers (x9 = s1 = mf, x14 = the shadow base, x19 = s3 = shadow(SF), x20 = s4 = SF+288 = &ev,
   x25 = s9 = pl, x18 / x26 / x24 = major / minor / patch); 32..39 = pl[0..8); 40 = mf+136 (the record body's
   address); 41 = mf+160 (the record index). x10 = pl+2 and x11 = its shadow cell's address are set to the terms
   the shadow check at 0x80f20 reads. Region 0: the machine frame's pointer slots, read only; region 1: the counter
   slot mf+208 (put_dec's p), writable; region 2: pl[0..8), read only. *)
Definition d3_SB : Z := 0x7fff8000.
Definition d3_Bx : sv := SOff 14 0.
Definition d3_Bspan : Z * Z := (d3_SB, d3_SB + 2 ^ 44 - 1).
Definition d3_mf : YP09.region := YP09.mkRegion (Some 9%nat) 32 184 32 32
  [YP09.mkChunk 32 (CVal 8 (SOff 20 (-64))); YP09.mkChunk 48 (CVal 8 (SOff 20 144));
   YP09.mkChunk 72 (CVal 8 (SOff 20 0)); YP09.mkChunk 88 (CVal 8 (SOff 20 (-256)));
   YP09.mkChunk 136 (CVal 8 (SOff 40 0)); YP09.mkChunk 152 (CVal 8 (SOff 25 0));
   YP09.mkChunk 160 (CVal 8 (SOff 41 0)); YP09.mkChunk 176 (CVal 8 (SOff 14 0))].
Definition d3_en : YP09.region := YP09.mkRegion (Some 9%nat) 208 216 208 216 [].
Definition d3_plr : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 1 (CVal 1 (SOff 33 0));
   YP09.mkChunk 2 (CVal 1 (SOff 34 0)); YP09.mkChunk 3 (CVal 1 (SOff 35 0));
   YP09.mkChunk 4 (CVal 1 (SOff 36 0)); YP09.mkChunk 5 (CVal 1 (SOff 37 0));
   YP09.mkChunk 6 (CVal 1 (SOff 38 0)); YP09.mkChunk 7 (CVal 1 (SOff 39 0))].
Definition d3_facts0 : facts :=
  mkFacts [(14%nat, mkAF d3_SB d3_SB 0); (25%nat, mkAF 4096 (2 ^ 47 - 16) 3);
           (9%nat, mkAF 0x7fff7f804000 (2 ^ 47) 5); (20%nat, mkAF 4096 (2 ^ 47 - 736) 5);
           (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
           (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0)] [] [].
Definition d3_r11 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 2) (SLit 3)) (SOff 14 0).
Definition d3_ss00 : sstate := mkSS 0x814 sr_atoms [d3_mf; d3_en; d3_plr] None d3_facts0.
Definition d3_ss0 : sstate :=
  mkSS 0x814 (sr_set (sr_set sr_atoms 10%bv (SOff 25 2)) 11%bv d3_r11) [d3_mf; d3_en; d3_plr] None d3_facts0.
Definition d3_SH0 : list shent := [mkSHE 25 0 8].
Definition d3_extra (bs : list byte) (BODY I : Z) : list word :=
  map (fun j => Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb bs j))) (seq 0 8) ++ [Z_to_bv 64 BODY; Z_to_bv 64 I].
(* The frame's shadow, base s3 (atom 19): the cells of `v` and `ev` (s3+28..s3+30, s3+36..s3+38), written only
   by plain runs. *)
Definition d3_sh : YP09.region := YP09.mkRegion (Some 19%nat) 28 39 28 39 [].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Definition d3_E (regs : bvmap 5 word) (bs : list byte) (BODY I : Z) : env := Eimg (Ereg regs (d3_extra bs BODY I)).

Lemma d3_set_reg : forall E ss ms (r : bv 5) e,
  st_ok_pi SEGS VAL E ss ms -> bv_eqb r 0 = false -> sv_denot E e = getr (ms_regs ms) r ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr0 He. unfold st_ok_pi, abs_ss, setpc in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
  (sr_set (ss_regs ss) r e) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. rewrite He.
  exact (st_ok_reg SEGS E _ ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma d3_garr8_byte : forall m a (bs : list byte) j,
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) bs) -> (j < length bs)%nat ->
  val_mem SEGS m (a + Z.of_nat j) 1 (RcIdentModel.bz (RcIdentModel.nthb bs j)).
Proof.
intros m a bs j Hb Hj. destruct (Hb j ltac:(rewrite length_map; exact Hj)) as [Hv _].
unfold RcIdentModel.bz, RcIdentModel.nthb, RcIdentModel.zb.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv by (rewrite length_map; exact Hj).
rewrite map_nth in Hv. exact Hv.
Qed.
Lemma d3_vm_mod64 : forall m a v, val_mem SEGS m a 8 v -> val_mem SEGS m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte.
assert (P : 2 ^ (8 * Z.of_nat 8) = 2 ^ 64) by reflexivity. rewrite !P.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* The symbolic state at 0x80f20 from the boundary's facts. *)
Lemma d3_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem mf pl SF BODY IX (bs : list byte),
  getr regs 9 = w64 mf -> getr regs 20 = w64 (SF + 288) -> getr regs 25 = w64 pl ->
  getr regs 14 = w64 SHADOW_OFF -> getr regs 10 = w64 (pl + 2) -> getr regs 11 = w64 (shadow_addr (pl + 2)) ->
  0x7fff7f804000 <= mf <= 2 ^ 47 - 320 -> mf mod 32 = 0 ->
  4096 <= SF -> SF + 1024 <= 2 ^ 47 -> SF mod 64 = 0 ->
  4096 <= pl -> pl + 16 <= mf -> pl <= 2 ^ 47 - 16 -> pl mod 8 = 0 -> 0 <= IX < 2 ^ 64 ->
  val_mem SEGS (rd W mem) (mf + 32) 8 (SF + 224) -> val_mem SEGS (rd W mem) (mf + 48) 8 (SF + 432) ->
  val_mem SEGS (rd W mem) (mf + 72) 8 (SF + 288) -> val_mem SEGS (rd W mem) (mf + 88) 8 (SF + 32) ->
  val_mem SEGS (rd W mem) (mf + 136) 8 BODY -> val_mem SEGS (rd W mem) (mf + 152) 8 pl ->
  val_mem SEGS (rd W mem) (mf + 160) 8 IX -> val_mem SEGS (rd W mem) (mf + 176) 8 SHADOW_OFF ->
  (forall j, (j < 8)%nat -> val_mem SEGS (rd W mem) (pl + Z.of_nat j) 1 (RcIdentModel.bz (RcIdentModel.nthb bs j))) ->
  (forall o, 208 <= o < 216 -> apresent (w_H W) mem (mf + o)) ->
  st_ok_pi SEGS VAL (d3_E regs bs BODY IX) d3_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x814)) mem (seg_rom SEGS))).
Proof.
intros W regs mem mf pl SF BODY IX bs H9 H20 H25 H14 H10 H11 Hmf Hmf32 HSF0 HSF1 HSF64 Hpl0 Hplmf Hpl1 Hpl8 HI
  V32 V48 V72 V88 V136 V152 V160 V176 VB HEN.
set (E := d3_E regs bs BODY IX).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (d3_extra bs BODY IX)) n)
  by (intros n Hn; subst E; unfold d3_E; apply Eimg_low; exact Hn).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite EL by (pose proof (u5_range r); unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hn)).
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (d3_extra bs BODY IX) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ j)).
assert (E9 : ew E 9 = Z_to_bv 64 mf) by (rewrite (ER 9%nat 9%bv eq_refl); exact H9).
assert (E14 : ew E 14 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 14%nat 14%bv eq_refl); exact H14).
assert (E20 : ew E 20 = Z_to_bv 64 (SF + 288)) by (rewrite (ER 20%nat 20%bv eq_refl); exact H20).
assert (E25 : ew E 25 = Z_to_bv 64 pl) by (rewrite (ER 25%nat 25%bv eq_refl); exact H25).
assert (E40 : ew E 40 = Z_to_bv 64 BODY) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E 41 = Z_to_bv 64 IX) by exact (EX 9%nat ltac:(lia)).
assert (EB : forall j, (j < 8)%nat -> ew E (32 + j) = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb bs j))).
{ intros j Hj. rewrite (EX j ltac:(lia)). unfold d3_extra.
  do 8 (destruct j as [|j]; [reflexivity|]). lia. }
pose proof (fun j : nat => SlotModel.bz_range (RcIdentModel.nthb bs j)) as RB.
assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U14 : bv_unsigned (ew E 14) = SHADOW_OFF) by (rewrite E14; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U20 : bv_unsigned (ew E 20) = SF + 288) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = pl) by (rewrite E25; apply unsigned_lit_small; lia).
assert (CH : forall base off a X, ew E a = Z_to_bv 64 X -> val_mem SEGS (rd W mem) (base + off) 8 X ->
  YP09.chunk_ok SEGS E (rd W mem) base {| c_off := off; YP09.c_val := CVal 8 (SOff a 0) |}).
{ intros base off a X Ha HX. apply (chunk_ok_val SEGS E _ base off 8 (SOff a 0) (X mod 2 ^ 64)).
  - cbn [sv_denot]. rewrite Ha, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply d3_Z_to_bv_mod64.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
  - cbn. lia.
  - exact (d3_vm_mod64 _ _ _ HX). }
assert (CHo : forall base off a c X, ew E a = Z_to_bv 64 (X - c) -> val_mem SEGS (rd W mem) (base + off) 8 X ->
  0 <= X < 2 ^ 64 -> 0 <= X - c < 2 ^ 64 ->
  YP09.chunk_ok SEGS E (rd W mem) base {| c_off := off; YP09.c_val := CVal 8 (SOff a c) |}).
{ intros base off a c X Ha HX HX0 HX1. apply (chunk_ok_val SEGS E _ base off 8 (SOff a c) X).
  - cbn [sv_denot]. rewrite Ha, unsigned_lit_small by lia. f_equal. lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
  - exact HX. }
assert (HS0 : st_ok_pi SEGS VAL E d3_ss00 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x814)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d3_ss00. apply pa_entry_st_ok_full.
  - subst E. unfold d3_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold d3_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (CHo mf 32 20%nat (-64) (SF + 224)); [rewrite E20; f_equal; lia | exact V32 | lia | lia].
      * apply (CHo mf 48 20%nat 144 (SF + 432)); [rewrite E20; f_equal; lia | exact V48 | lia | lia].
      * apply (CHo mf 72 20%nat 0 (SF + 288)); [rewrite E20; f_equal; lia | exact V72 | lia | lia].
      * apply (CHo mf 88 20%nat (-256) (SF + 32)); [rewrite E20; f_equal; lia | exact V88 | lia | lia].
      * apply (CH mf 136 40%nat BODY E40 V136).
      * apply (CHo mf 152 25%nat 0 pl); [rewrite E25; f_equal; lia | exact V152 | lia | lia].
      * apply (CH mf 160 41%nat IX E41 V160).
      * apply (CHo mf 176 14%nat 0 SHADOW_OFF); [rewrite E14; f_equal; lia | exact V176 | unfold SHADOW_OFF; lia
        | unfold SHADOW_OFF; lia].
    + unfold d3_en, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HEN. exact Ho.
    + unfold d3_plr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      assert (CB : forall j : nat, (j < 8)%nat ->
        YP09.chunk_ok SEGS E (rd W mem) pl {| c_off := Z.of_nat j; YP09.c_val := CVal 1 (SOff (32 + j) 0) |}).
      { intros j Hj. apply (chunk_ok_val SEGS E _ pl (Z.of_nat j) 1 (SOff (32 + j) 0)
          (RcIdentModel.bz (RcIdentModel.nthb bs j))).
        - cbn [sv_denot]. rewrite (EB j Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - change (2 ^ (8 * Z.of_N 1)) with 256. exact (RB j).
        - cbn. lia.
        - exact (VB j Hj). }
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (CB 0%nat ltac:(lia)).
      * exact (CB 1%nat ltac:(lia)).
      * exact (CB 2%nat ltac:(lia)).
      * exact (CB 3%nat ltac:(lia)).
      * exact (CB 4%nat ltac:(lia)).
      * exact (CB 5%nat ltac:(lia)).
      * exact (CB 6%nat ltac:(lia)).
      * exact (CB 7%nat ltac:(lia)).
  - apply pairwise_disjoint_of_extents. unfold d3_mf, d3_en, d3_plr, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - unfold facts_ok, d3_facts0. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U14, U20, U25.
    pose proof (EB 0%nat ltac:(lia)) as EB0. pose proof (EB 1%nat ltac:(lia)) as EB1.
    pose proof (EB 2%nat ltac:(lia)) as EB2. pose proof (EB 3%nat ltac:(lia)) as EB3.
    pose proof (EB 4%nat ltac:(lia)) as EB4. pose proof (EB 5%nat ltac:(lia)) as EB5.
    pose proof (EB 6%nat ltac:(lia)) as EB6. pose proof (EB 7%nat ltac:(lia)) as EB7.
    cbn [Nat.add] in EB0, EB1, EB2, EB3, EB4, EB5, EB6, EB7.
    rewrite EB0, EB1, EB2, EB3, EB4, EB5, EB6, EB7.
    rewrite !unsigned_lit_small by (pose proof (RB 0%nat); pose proof (RB 1%nat); pose proof (RB 2%nat);
      pose proof (RB 3%nat); pose proof (RB 4%nat); pose proof (RB 5%nat); pose proof (RB 6%nat); pose proof (RB 7%nat);
      lia).
    pose proof (RB 0%nat); pose proof (RB 1%nat); pose proof (RB 2%nat); pose proof (RB 3%nat);
    pose proof (RB 4%nat); pose proof (RB 5%nat); pose proof (RB 6%nat); pose proof (RB 7%nat).
    unfold d3_SB, SHADOW_OFF. change (2 ^ 3) with 8. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia. }
assert (HS1 := d3_set_reg E d3_ss00 _ 10%bv (SOff 25 2) HS0 eq_refl
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite E25, H10; unfold w64; f_equal; rewrite unsigned_lit_small by lia; lia)).
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts d3_ss00] in HS1.
assert (HS2 := d3_set_reg E _ _ 11%bv d3_r11 HS1 eq_refl).
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. apply HS2.
cbn [ms_regs restrict mkst]. rewrite H11. rewrite denot_lit_U. unfold w64. f_equal.
unfold d3_r11. rewrite U_SAlu, U_SAlu, (U_atom_off E 25 pl 2 E25 ltac:(lia) ltac:(lia)), U_SLit,
  (U_atom E 14 SHADOW_OFF E14 ltac:(unfold SHADOW_OFF; lia)).
cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (pl + 2) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
rewrite (zcanon_id ((pl + 2) / 8)) by (unfold M64; lia).
unfold shadow_addr, SHADOW_OFF. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* A byte or word the symbolic state knows, as a fact of memory. *)
Lemma d3_chunk_val : forall E (rs : smem) m n lo hi wl wh cs o (w : N) e v,
  mem_ok SEGS E m rs -> In (YP09.mkRegion (Some n) lo hi wl wh cs) rs -> In (YP09.mkChunk o (CVal w e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (bv_unsigned (ew E n) + o) (N.to_nat w) v.
Proof.
intros E rs m n lo hi wl wh cs o w e v Hm Hin Hc He Hv.
pose proof (mem_ok_region SEGS E m rs _ Hm Hin) as (_ & _ & _ & Hch).
rewrite Forall_forall in Hch. specialize (Hch _ Hc).
intros kk Hkk. cbn [YP09.r_base base_val] in Hch.
exact (YN0d.chunk_bytes_cval_exact SEGS E m _ o w e v Hch He Hv kk Hkk).
Qed.
Lemma d3_aview_of_vm1 : forall H m a v, val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview SEGS H m a = Some v.
Proof. intros H m a v Hv Hr. exact (aview_of_val_mem1 SEGS H m a v Hv Hr). Qed.
(* `ev`'s and `v`'s bytes are addressable once their shadow cells hold 0 (ev: s3+36..38; v: s3+28, 29 and the
   partial cell s3+30 = 4). *)
Lemma d3_ev_addr : forall (rd : reader) SF q n, SF mod 8 = 0 ->
  (forall j, 0 <= j < 3 -> rd (shadow_addr SF + 36 + j) = Some 0) -> SF + 288 <= q -> q + n <= SF + 312 ->
  range_addressable rd SHADOW_OFF q n.
Proof.
intros rd SF q n H8 Hz Hq Hn x Hx. exists 0. split; [|left; reflexivity].
replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr SF + 36 + (x / 8 - SF / 8 - 36))
  by (unfold shadow_of_addr, shadow_addr; lia).
apply Hz. lia.
Qed.
Lemma d3_v_addr : forall (rd : reader) SF q n, SF mod 8 = 0 ->
  rd (shadow_addr SF + 28) = Some 0 -> rd (shadow_addr SF + 29) = Some 0 -> rd (shadow_addr SF + 30) = Some 4 ->
  SF + 224 <= q -> q + n <= SF + 244 ->
  range_addressable rd SHADOW_OFF q n.
Proof.
intros rd SF q n H8 Z28 Z29 Z30 Hq Hn x Hx.
assert (Ex : shadow_of_addr SHADOW_OFF x = shadow_addr SF + (x / 8 - SF / 8)) by (unfold shadow_of_addr, shadow_addr; lia).
rewrite Ex. assert (28 <= x / 8 - SF / 8 <= 30) by lia.
destruct (Z.eq_dec (x / 8 - SF / 8) 28) as [E|E]; [rewrite E; exists 0; split; [exact Z28 | left; reflexivity]|].
destruct (Z.eq_dec (x / 8 - SF / 8) 29) as [E'|E']; [rewrite E'; exists 0; split; [exact Z29 | left; reflexivity]|].
replace (x / 8 - SF / 8) with 30 by lia. exists 4. split; [exact Z30|]. right. lia.
Qed.

Lemma d3_vm4_bytes : forall m a b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  val_mem SEGS m a 4 (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) -> garr8 SEGS m a [b0; b1; b2; b3].
Proof.
intros m a b0 b1 b2 b3 R0 R1 R2 R3 Hv.
assert (Lk : forall (k : nat) bk, (k < 4)%nat ->
  ((b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) / 2 ^ (8 * Z.of_nat k)) mod 256 = bk -> 0 <= bk < 256 ->
  val_mem SEGS m (a + Z.of_nat k) 1 bk /\ 0 <= bk < 256).
{ intros k bk Hk Hle Hr. split; [|exact Hr]. intros kk Hkk. assert (kk = 0%nat) by lia. subst kk.
  rewrite Z.add_0_r. rewrite (Hv k Hk). f_equal. f_equal. unfold YO0f.le_byte.
  change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite (Z.mod_small _ (2 ^ 32)) by lia.
  change (2 ^ 0) with 1. rewrite Z.div_1_r. rewrite Hle. rewrite !Z.mod_small by lia. reflexivity. }
intros j Hj. cbn [length] in Hj.
destruct j as [|[|[|[|j]]]]; cbn [nth]; [apply Lk | apply Lk | apply Lk | apply Lk | lia]; try lia.
all: first [ change (2 ^ (8 * Z.of_nat 0)) with 1 | change (2 ^ (8 * Z.of_nat 1)) with 256
           | change (2 ^ (8 * Z.of_nat 2)) with 65536 | change (2 ^ (8 * Z.of_nat 3)) with 16777216 ];
  Z.div_mod_to_equations; lia.
Qed.
Lemma d3_garr8_app : forall m a l1 l2, garr8 SEGS m a l1 -> garr8 SEGS m (a + Z.of_nat (length l1)) l2 ->
  garr8 SEGS m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [L|L].
- rewrite app_nth1 by exact L. exact (H1 j L).
- rewrite app_nth2 by exact L. destruct (H2 (j - length l1)%nat ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
  replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. exact Hv.
Qed.
Lemma d3_first8 : forall (l : list byte), (8 <= length l)%nat ->
  map (fun b : byte => bv_unsigned b) (firstn 8 l) =
  [RcIdentModel.bz (RcIdentModel.nthb l 0); RcIdentModel.bz (RcIdentModel.nthb l 1);
   RcIdentModel.bz (RcIdentModel.nthb l 2); RcIdentModel.bz (RcIdentModel.nthb l 3);
   RcIdentModel.bz (RcIdentModel.nthb l 4); RcIdentModel.bz (RcIdentModel.nthb l 5);
   RcIdentModel.bz (RcIdentModel.nthb l 6); RcIdentModel.bz (RcIdentModel.nthb l 7)].
Proof.
intros l Hl. do 8 (destruct l as [|? l]; [cbn in Hl; lia|]). reflexivity.
Qed.

Lemma d3_ge_taken : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true.
Proof.
intros E n v Hn Hv. rewrite YO0c.branch_ge. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by lia. rewrite (unsigned_lit_small 0) by lia. rewrite !YO0b.s64_small by lia.
apply negb_true_iff, Z.ltb_ge. lia.
Qed.
Lemma d3_eq_taken : forall E n1 n2 v, ew E n1 = Z_to_bv 64 v -> ew E n2 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n1 0)) (sv_denot E (SOff n2 0)) = true.
Proof.
intros E n1 n2 v H1 H2 Hv. rewrite branch_eq_U, (U_atom E n1 v H1 Hv), (U_atom E n2 v H2 Hv). apply Z.eqb_refl.
Qed.
Lemma d3_eq0_false : forall E n (w : word), ew E n = w ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> w <> w64 0.
Proof.
intros E n w Hn Hb Hw. rewrite branch_eq_U in Hb. apply Z.eqb_neq in Hb. apply Hb.
unfold U. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned, Hw. reflexivity.
Qed.

Lemma d3_garr8_1 : forall m a v, val_mem SEGS m a 1 v -> 0 <= v < 256 -> garr8 SEGS m a [v].
Proof.
intros m a v Hv Hr j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth].
rewrite Z.add_0_r. split; [exact Hv | exact Hr].
Qed.
Lemma d3_garr8_aview : forall H m a l j, garr8 SEGS (mrestrict H m) a l -> (j < length l)%nat ->
  aview SEGS H m (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. exact (aview_of_val_mem1 SEGS H m _ _ Hv Hr).
Qed.
Lemma d3_bcmp_eq : forall H m a1 a2 l, garr8 SEGS (mrestrict H m) a1 l -> garr8 SEGS (mrestrict H m) a2 l ->
  forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H m (a1 + i) = aview SEGS H m (a2 + i).
Proof.
intros H m a1 a2 l G1 G2 i Hi.
assert (Hj : (Z.to_nat i < length l)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by (destruct Hi; assumption); destruct Hi; assumption).
replace i with (Z.of_nat (Z.to_nat i)) by (apply Z2Nat.id; destruct Hi; assumption).
rewrite (d3_garr8_aview H m a1 l _ G1 Hj), (d3_garr8_aview H m a2 l _ G2 Hj). reflexivity.
Qed.
Lemma d3_garr8_app' : forall m a l1 a2 l2, garr8 SEGS m a l1 -> a2 = a + Z.of_nat (length l1) -> garr8 SEGS m a2 l2 ->
  garr8 SEGS m a (l1 ++ l2).
Proof. intros m a l1 a2 l2 H1 -> H2. exact (d3_garr8_app m a l1 l2 H1 H2). Qed.
Lemma d3_bytes_eq : forall ma mi pa, 0 <= ma < 65536 -> 0 <= mi < 65536 -> 0 <= pa < 65536 ->
  rvs_bytes ma mi pa = map (fun b : byte => bv_unsigned b) (IdentSpec.DEC ma 1) ++ [46] ++
    map (fun b : byte => bv_unsigned b) (IdentSpec.DEC mi 1) ++ map (fun b : byte => bv_unsigned b) (IdentSpec.DEC pa 2) ++ [0].
Proof.
intros ma mi pa H1 H2 H3. unfold rvs_bytes. rewrite <- (d3_EV_VER ma mi pa H1 H2 H3). unfold d3_EV.
rewrite !map_app. cbn [map]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma d3_ra_hw : forall (rd : reader) SF, SF mod 8 = 0 ->
  rd (shadow_addr SF + 54) = Some 0 -> rd (shadow_addr SF + 55) = Some 4 ->
  range_addressable rd SHADOW_OFF (SF + 432) 12.
Proof.
intros rd SF H8 Z54 Z55 x Hx.
assert (Ex : shadow_of_addr SHADOW_OFF x = shadow_addr SF + (x / 8 - SF / 8)) by (unfold shadow_of_addr, shadow_addr; lia).
rewrite Ex. assert (54 <= x / 8 - SF / 8 <= 55) by lia.
destruct (Z.eq_dec (x / 8 - SF / 8) 54) as [E|E]; [rewrite E; exists 0; split; [exact Z54 | left; reflexivity]|].
replace (x / 8 - SF / 8) with 55 by lia. exists 4. split; [exact Z55|]. right. lia.
Qed.

Section c.
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* What this segment needs, each with the contract's name and text (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Hypothesis HVS : reac_identity_reac_ver_str.treac_identity_reac_ver_str_spec B.
Hypothesis HPD : put_dec.tput_dec_spec B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* The machine stack's shadow is 0 (AR's zero-shadow ranges, the stack first). *)
Lemma d3_stack_src : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= a -> a + 72 <= sp0 -> a mod 8 = 0 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF a 8 /\ shadow_hull_vis (aview SEGS (w_H W) memc) a 8.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ Ha0 Ha1 Ha8.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
pose proof (al_zshadow _ _ LAWS lyc Sc W memc mdc (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
  HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
unfold page_aligned in Hpal, Hpah. rewrite Elo, Ehi in *.
pose proof asan_consts as (C1 & _).
set (lo := ly_stk_lo ly) in *. set (hi := ly_stk_hi ly) in *.
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  assert (Ex : shadow_of_addr SHADOW_OFF x = shadow_of_addr SHADOW_OFF lo + (x / 8 - lo / 8))
    by (unfold shadow_of_addr; lia).
  rewrite Ex. apply Hz. lia.
- intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
  assert (Es : s = shadow_of_addr SHADOW_OFF lo + (s - (SHADOW_OFF + lo / 8))) by (unfold shadow_of_addr; lia).
  rewrite Es, (Hz (s - (SHADOW_OFF + lo / 8))); [discriminate|]. unfold SHADOW_OFF. lia.
Qed.

(* put_dec(ev, &en, v, mn) at a slot of this segment: the callee's contract (HPD, through PSIG) with every
   premise the walk's state gives. *)
Lemma d3_putdec : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdT lyc Sc kk n v mn retk,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    lyc Sc W memT mdT kk ->
  frames Sc = [(4, pos)] -> st_nev Sc <= EV_MAX ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 -> alloc_ceiling + 16384 <= mf ->
  4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling -> in_app (SFa g pos) 1024 -> SFa g pos mod 64 = 0 ->
  getr regsT 10 = w64 (SFa g pos + 288) -> getr regsT 11 = w64 (mf + 208) -> getr regsT 12 = w64 v ->
  getr regsT 13 = w64 mn -> getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsT 2 = w64 mf -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  0 <= v < 65536 -> 1 <= mn <= 2 -> 0 <= n -> n + put_dec_c.dec_len v mn <= 24 ->
  val_mem SEGS (rd W memT) (mf + 208) 8 n ->
  (forall j, 0 <= j < 3 -> aview SEGS (w_H W) memT (shadow_addr (SFa g pos) + 36 + j) = Some 0) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IS_put_dec)) memT (seg_rom SEGS)) mdT)
    (tput_dec_post B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
      lyc Sc W memT kk regsT (SFa g pos + 288) (mf + 208) n v mn).
Proof.
intros g pos mf W regsT memT mdT lyc Sc kk n v mn retk HJ Hfr Hnev Hmf Hmf32 Hmf0 HSF0 HSF1 HSFapp HSF64
  R10 R11 R12 R13 R1 Hrk Hrk2 R2 R3 R4 Hv Hmn Hn Hnd Vn Hevz.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr lyc 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *. set (sp0 := e_sp0 g) in *.
pose proof (d3_dl1 v Hv) as Hd1. pose proof (d3_dl2 v Hv) as Hd2.
assert (Hdl : 1 <= put_dec_c.dec_len v mn <= 5) by (destruct (Z.eq_dec mn 1) as [->|]; [lia | replace mn with 2 by lia; lia]).
assert (Usp : spZ regsT = mf) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp.
rewrite (PSIG IS_put_dec AF_put_dec eq_refl).
change (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_put_dec)) memT (seg_rom SEGS)) mdT)
  with (cfg_at SEGS (BASE + AF_put_dec) regsT memT mdT).
assert (HWR : forall a, awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) lyc [(4, pos)] a ->
  ~ (mf - ESTACK <= a < mf) ->
  awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) lyc [(4, pos)] a /\
  apresent (w_H W) memT a /\ ~ aowned B lyc Sc a /\ ~ (mf - ESTACK <= a < mf)).
{ intros a Ha Hw. destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Ha) as [Hp Ho].
  split; [exact Ha|]. split; [exact Hp|]. split; [exact Ho | exact Hw]. }
assert (HFRM : forall a, SF <= a < SF + 1024 ->
  awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) lyc [(4, pos)] a).
{ intros a Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
  unfold in_zr. rewrite EFa, HFB. cbn [fst snd]. lia. }
assert (HSTKW : forall a, sp0 - LLVMF_STK <= a < sp0 ->
  awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) lyc [(4, pos)] a)
  by (intros a Ha; left; exact Ha).
destruct (d3_stack_src _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mf + 208) HJ ltac:(lia) ltac:(lia)
  ltac:(clear - Hmf32; lia)) as [HRAp HHp].
apply HPD.
- exact HJ.
- rewrite R1. apply ret_ok_codeptr_v; [exact Hrk | exact Hrk2].
- unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
- exact R3.
- exact R4.
- exact R10.
- exact R11.
- rewrite R12. unfold w64. rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
- left. rewrite R12. unfold w64. rewrite unsigned_lit_small by lia. lia.
- exact R13.
- lia.
- rewrite Usp. exact Hmf32.
- rewrite Usp. unfold PUT_DEC_STK, ESTACK. lia.
- rewrite Usp. lia.
- rewrite Hfr. cbn. lia.
- clear - Hmf32. lia.
- lia.
- exact Hn.
- exact Vn.
- rewrite Usp. intros a Ha. apply HWR; [apply HSTKW; lia | lia].
- rewrite Usp. intros a Ha. apply HWR; [apply HFRM; lia | lia].
- rewrite Usp. split; [|split; [exact HRAp | split; [exact HHp|]]].
  + intros a Ha. split; [|lia]. apply (aview_some_of_apresent SEGS). apply Hpres. lia.
  + split; [right; unfold kHighMemBeg, kHighMemEnd; lia | lia].
- rewrite Usp. split; [|split; [|split]].
  + intros a Ha. split; [|lia]. apply (aview_some_of_apresent SEGS).
    exact (proj1 (proj2 (HWR a (HFRM a ltac:(lia)) ltac:(lia)))).
  + apply (d3_ev_addr _ SF); [clear - HSF64; lia | exact Hevz | lia | lia].
  + apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memT mdT 4 pos);
      [exact HAR | rewrite Hfr; left; reflexivity | rewrite EFa; lia | rewrite EFa, HFB; lia | lia].
  + split; [|lia]. apply amem_range_high; [lia | | lia].
    destruct HSFapp as [_ [HL | (HH1 & HH2)]]; [left; lia | right; lia].
- right. lia.
- left. rewrite Usp. lia.
- right. rewrite Usp. unfold PUT_DEC_STK, ESTACK. lia.
- unfold EV_PUT_DEC. lia.
Qed.

(* reac_identity_reac_ver_str(major, minor, patch, v, 20) at 0x81094. *)
Lemma d3_verstr : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdT lyc Sc kk ma mi pa retk,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    lyc Sc W memT mdT kk ->
  frames Sc = [(4, pos)] ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 -> alloc_ceiling + 16384 <= mf ->
  4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling -> SFa g pos mod 64 = 0 ->
  getr regsT 10 = w64 ma -> getr regsT 11 = w64 mi -> getr regsT 12 = w64 pa ->
  getr regsT 13 = w64 (SFa g pos + 224) -> getr regsT 14 = w64 20 ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsT 2 = w64 mf -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  0 <= ma < 65536 -> 0 <= mi < 65536 -> 0 <= pa < 65536 ->
  aview SEGS (w_H W) memT (shadow_addr (SFa g pos) + 28) = Some 0 ->
  aview SEGS (w_H W) memT (shadow_addr (SFa g pos) + 29) = Some 0 ->
  aview SEGS (w_H W) memT (shadow_addr (SFa g pos) + 30) = Some 4 ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IS_reac_identity_reac_ver_str)) memT (seg_rom SEGS)) mdT)
    (treac_identity_reac_ver_str_post B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] lyc Sc W memT kk regsT ma mi pa (SFa g pos + 224) 20).
Proof.
intros g pos mf W regsT memT mdT lyc Sc kk ma mi pa retk HJ Hfr Hmf Hmf32 Hmf0 HSF0 HSF1 HSF64
  R10 R11 R12 R13 R14 R1 Hrk Hrk2 R2 R3 R4 Hma Hmi Hpa Z28 Z29 Z30.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr lyc 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *. set (sp0 := e_sp0 g) in *.
assert (Usp : spZ regsT = mf) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
rewrite (PSIG IS_reac_identity_reac_ver_str AF_reac_identity_reac_ver_str eq_refl).
change (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_reac_identity_reac_ver_str)) memT (seg_rom SEGS)) mdT)
  with (cfg_at SEGS (BASE + AF_reac_identity_reac_ver_str) regsT memT mdT).
apply HVS.
- exact HJ.
- rewrite R1. apply ret_ok_codeptr_v; [exact Hrk | exact Hrk2].
- unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
- exact R3.
- exact R4.
- rewrite Usp. clear - Hmf32. lia.
- rewrite Usp. unfold REAC_VER_STR_STK, WRITE_UINT_STK, ESTACK. lia.
- rewrite Usp. lia.
- exact R10.
- exact R11.
- exact R12.
- exact R13.
- exact R14.
- exact Hma.
- exact Hmi.
- exact Hpa.
- lia.
- lia.
- intros _. split; [|split].
  + rewrite Usp. intros a Ha.
    assert (Hw : awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) lyc [(4, pos)] a).
    { right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
      unfold in_zr. rewrite EFa, HFB. cbn [fst snd]. lia. }
    destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
    split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|]. lia.
  + right. exists 4, pos. split; [rewrite Hfr; left; reflexivity|]. rewrite EFa, HFB. lia.
  + apply (d3_v_addr _ SF); [clear - HSF64; lia | exact Z28 | exact Z29 | exact Z30 | lia | lia].
- rewrite Hfr. cbn. lia.
Qed.

(* bcmp(v, ev, n) at 0x810b8 (YCbq.aj_bcmp_at). *)
Lemma d3_bcmp : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdT lyc Sc kk n retk,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    lyc Sc W memT mdT kk ->
  frames Sc = [(4, pos)] ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 -> alloc_ceiling + 16384 <= mf ->
  4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling -> in_app (SFa g pos) 1024 -> SFa g pos mod 64 = 0 ->
  getr regsT 10 = w64 (SFa g pos + 224) -> getr regsT 11 = w64 (SFa g pos + 288) -> getr regsT 12 = w64 n ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsT 2 = w64 mf -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  1 <= n <= 20 ->
  aview SEGS (w_H W) memT (shadow_addr (SFa g pos) + 28) = Some 0 ->
  aview SEGS (w_H W) memT (shadow_addr (SFa g pos) + 29) = Some 0 ->
  aview SEGS (w_H W) memT (shadow_addr (SFa g pos) + 30) = Some 4 ->
  (forall j, 0 <= j < 3 -> aview SEGS (w_H W) memT (shadow_addr (SFa g pos) + 36 + j) = Some 0) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
      lyc Sc W mem2 md2 kk /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
    (v = w64 0 <-> forall i, 0 <= i < n ->
       aview SEGS (w_H W) memT (SFa g pos + 224 + i) = aview SEGS (w_H W) memT (SFa g pos + 288 + i)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros g pos mf W regsT memT mdT lyc Sc kk n retk HJ Hfr Hmf Hmf32 Hmf0 HSF0 HSF1 HSFapp HSF64
  R10 R11 R12 R1 Hrk Hrk2 R2 R3 R4 Hn Z28 Z29 Z30 Hevz.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr lyc 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *. set (sp0 := e_sp0 g) in *.
assert (Usp : spZ regsT = mf) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp.
assert (HPF : forall a, SF <= a < SF + 1024 -> apresent (w_H W) memT a).
{ intros a Ha.
  assert (Hw : awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyc Sc) lyc [(4, pos)] a).
  { right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
    unfold in_zr. rewrite EFa, HFB. cbn [fst snd]. lia. }
  exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw)). }
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA IS___interceptor_trampoline_bcmp) ABCMP W regsT memT
    LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc mdT kk (SF + 224) (SF + 288) n
    (mf - sp0) (Z_to_bv 64 (BASE + retk)) HJ).
  - exact R10. - exact R11. - exact R12. - lia.
  - lia. - lia. - lia. - lia.
  - rewrite Usp. lia. - clear - Hmf32 Hsp0al. lia. - lia. - unfold ESTACK. lia.
  - exact R3. - exact R4. - exact R1. - apply ret_ok_codeptr_v; [exact Hrk | exact Hrk2].
  - intros a Ha. rewrite Usp. split; [apply (aview_some_of_apresent SEGS); apply HPF; lia | lia].
  - intros a Ha. rewrite Usp. split; [apply (aview_some_of_apresent SEGS); apply HPF; lia | lia].
  - intros a Ha. unfold ESTACK. lia.
  - intros a Ha. unfold ESTACK. lia.
  - apply amem_range_high; [lia | | lia]. destruct HSFapp as [_ [HL | (HH1 & HH2)]]; [left; lia | right; lia].
  - apply amem_range_high; [lia | | lia]. destruct HSFapp as [_ [HL | (HH1 & HH2)]]; [left; lia | right; lia].
  - apply (d3_v_addr _ SF); [clear - HSF64; lia | exact Z28 | exact Z29 | exact Z30 | lia | lia].
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memT mdT 4 pos);
      [exact HAR | rewrite Hfr; left; reflexivity | rewrite EFa; lia | rewrite EFa, HFB; lia | lia].
  - apply (d3_ev_addr _ SF); [clear - HSF64; lia | exact Hevz | lia | lia].
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memT mdT 4 pos);
      [exact HAR | rewrite Hfr; left; reflexivity | rewrite EFa; lia | rewrite EFa, HFB; lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hc & Hk & Hp).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hv|]. split; [exact Hc|].
split; [|exact Hp]. intros a Ha Hna. apply Hk; [exact Ha | lia].
Qed.

(* What a caller-journal call kept, on the bytes this walk carries: the machine frame and above, the entry's
   class-4 frame and its shadow, and the heap blocks. *)
Lemma d3_tcj_keep : forall STK lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 sp (Ew : Z -> Prop) pos SF a,
  tcj_kept B STK lyc Sc W memc W2 mem2 sp Ew ->
  frames Sc = [(4, pos)] -> frame_addr lyc 4 pos = SF -> alloc_ceiling <= sp ->
  0 <= a < 2 ^ 64 ->
  (sp <= a \/ SF <= a < SF + 1024 \/ shadow_addr SF <= a < shadow_addr SF + 128 \/
   (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m)) ->
  ~ Ew a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros STK lyc Sc W memc W2 mem2 sp Ew pos SF a (K1 & K2 & _ & K4 & _) Hfr EFa Hsp Ha Hc HE.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
destruct Hc as [Hc | [Hc | [Hc | (b & m & Hin & Hb)]]].
- apply K1; [lia | lia | exact HE].
- apply (K4 4 pos a); [rewrite Hfr; left; reflexivity | | exact HE].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, HFB. lia.
- apply (K4 4 pos a); [rewrite Hfr; left; reflexivity | | exact HE].
  right. unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. change (1024 / 8) with 128. lia.
- replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
  replace (b + (a - b)) with a by lia. exact HE.
Qed.

Lemma d3_rk_ro : forall E H H' (m m' : word -> option byte) n b lo hi w cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H' m' a = aview SEGS H m a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H' m') (YP09.mkRegion (Some n) lo hi w w cs).
Proof.
intros E H H' m m' n b lo hi w cs Hn Hk.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hk. exact Ha.
- lia.
Qed.
Lemma d3_ext : forall E n1 lo1 hi1 wl1 wh1 cs1 n2 lo2 hi2 wl2 wh2 cs2 b1 b2,
  bv_unsigned (ew E n1) = b1 -> bv_unsigned (ew E n2) = b2 ->
  (b1 + hi1 <= b2 + lo2 \/ b2 + hi2 <= b1 + lo1) ->
  extent_disjoint E (YP09.mkRegion (Some n1) lo1 hi1 wl1 wh1 cs1) (YP09.mkRegion (Some n2) lo2 hi2 wl2 wh2 cs2).
Proof. intros. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. lia. Qed.

(* ---- what the segment keeps of the boundary's memory ---------------------------------------------------- *)
(* The bytes the boundary's facts live in (the machine frame and above, the class-4 frame and its shadow, the heap
   blocks of the start state) and the bytes the segment may write (mf+208, v .. ev, hw, the shadow cells of v
   and ev). Every step keeps the first outside the second. *)
Definition d3_cls (ly : alayout) (S : astate) (mf SF a : Z) : Prop :=
  mf <= a \/ SF <= a < SF + 1024 \/ shadow_addr SF <= a < shadow_addr SF + 128 \/
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= a < b + req_size m).
Definition d3_wr (mf SF a : Z) : Prop :=
  mf + 208 <= a < mf + 216 \/ SF + 224 <= a < SF + 312 \/ SF + 432 <= a < SF + 444 \/
  shadow_addr SF + 28 <= a < shadow_addr SF + 39.
Definition d3_kk (ly : alayout) (S : astate) (mf SF : Z) (W0 : world SEGS) (m0 : word -> option byte)
  (W' : world SEGS) (m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> d3_cls ly S mf SF a -> ~ d3_wr mf SF a ->
  aview SEGS (w_H W') m' a = aview SEGS (w_H W0) m0 a.
Lemma d3_kk_refl : forall ly S mf SF W m, d3_kk ly S mf SF W m W m.
Proof. intros ly S mf SF W m a _ _ _. reflexivity. Qed.
Lemma d3_kk_step : forall ly S mf SF W0 m0 W m W' m',
  d3_kk ly S mf SF W0 m0 W m ->
  (forall a, 0 <= a < 2 ^ 64 -> d3_cls ly S mf SF a -> ~ d3_wr mf SF a ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d3_kk ly S mf SF W0 m0 W' m'.
Proof. intros ly S mf SF W0 m0 W m W' m' HK HS a Ha Hc Hw. rewrite (HS a Ha Hc Hw). exact (HK a Ha Hc Hw). Qed.
Lemma d3_kk_tcj : forall ly S mf SF W0 m0 STK lyc Sc W m W' m' (Ew : Z -> Prop) pos,
  d3_kk ly S mf SF W0 m0 W m ->
  tcj_kept B STK lyc Sc W m W' m' mf Ew ->
  frames Sc = [(4, pos)] -> frame_addr lyc 4 pos = SF -> alloc_ceiling <= mf ->
  Permutation (ablocks B lyc Sc) (ablocks B ly S) -> (forall a, Ew a -> d3_wr mf SF a) ->
  d3_kk ly S mf SF W0 m0 W' m'.
Proof.
intros ly S mf SF W0 m0 STK lyc Sc W m W' m' Ew pos HK HT Hfr EFa Hmf Hperm HE.
apply (d3_kk_step ly S mf SF W0 m0 W m W' m' HK). intros a Ha Hc Hw.
apply (d3_tcj_keep STK lyc Sc W m W' m' mf Ew pos SF a HT Hfr EFa Hmf Ha); [|intros He; exact (Hw (HE a He))].
destruct Hc as [Hc | [Hc | [Hc | (b & mm & Hin & Hb)]]]; [left; exact Hc | right; left; exact Hc | right; right; left; exact Hc|].
right; right; right. exists b, mm. split; [|exact Hb]. exact (Permutation_in _ (Permutation_sym Hperm) Hin).
Qed.
Lemma d3_kk_frame : forall ly S mf SF W0 m0 (W : world SEGS) m m' E (rs : smem),
  d3_kk ly S mf SF W0 m0 W m ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> d3_wr mf SF a) ->
  d3_kk ly S mf SF W0 m0 W m'.
Proof.
intros ly S mf SF W0 m0 W m m' E rs HK HF Hw.
apply (d3_kk_step ly S mf SF W0 m0 W m W m' HK). intros a Ha _ Hna.
exact (kept_of_frame E rs (w_H W) m m' (d3_wr mf SF) HF Hw a Ha Hna).
Qed.

(* The shadow cells of v and ev: written by run 5 and by the last run only. *)
Definition d3_kc (SF : Z) (W0 : world SEGS) (m0 : word -> option byte) (W' : world SEGS) (m' : word -> option byte) : Prop :=
  forall c, 28 <= c < 39 -> aview SEGS (w_H W') m' (shadow_addr SF + c) = aview SEGS (w_H W0) m0 (shadow_addr SF + c).
Lemma d3_kc_refl : forall SF W m, d3_kc SF W m W m.
Proof. intros SF W m c _. reflexivity. Qed.
Definition d3_apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.
(* The shadow cells of the frame lie apart from the frame and below the machine frame: a write into the frame or
   at or above the machine frame keeps them. *)
Definition d3_shapart (SF mf : Z) : Prop :=
  (forall a, shadow_addr SF <= a < shadow_addr SF + 128 -> ~ (SF <= a < SF + 1024)) /\
  0 <= shadow_addr SF /\ shadow_addr SF + 128 <= mf /\ mf <= 2 ^ 64.
Lemma d3_kc_frame : forall SF mf W0 m0 (W : world SEGS) m m' E (rs : smem),
  d3_kc SF W0 m0 W m -> d3_shapart SF mf ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi ->
     SF <= a < SF + 1024 \/ mf <= a) ->
  d3_kc SF W0 m0 W m'.
Proof.
intros SF mf W0 m0 W m m' E rs HK (HA & H0 & H1 & H2) HF Hw c Hc. rewrite <- (HK c Hc).
apply (kept_of_frame E rs (w_H W) m m' (fun a => ~ (shadow_addr SF + 28 <= a < shadow_addr SF + 39)) HF); [|lia | lia].
intros b wlo whi a Hin Ha Hs. destruct (Hw b wlo whi a Hin Ha) as [X|X]; [exact (HA a ltac:(lia) X) | lia].
Qed.
Lemma d3_kc_tcj : forall SF mf W0 m0 STK lyc Sc W m W' m' (Ew : Z -> Prop) pos,
  d3_kc SF W0 m0 W m -> tcj_kept B STK lyc Sc W m W' m' mf Ew ->
  frames Sc = [(4, pos)] -> frame_addr lyc 4 pos = SF -> alloc_ceiling <= mf -> d3_shapart SF mf ->
  (forall a, Ew a -> SF <= a < SF + 1024 \/ mf <= a) ->
  d3_kc SF W0 m0 W' m'.
Proof.
intros SF mf W0 m0 STK lyc Sc W m W' m' Ew pos HK HT Hfr EFa Hsp (HA & H0 & H1 & H2) HE c Hc. rewrite <- (HK c Hc).
apply (d3_tcj_keep STK lyc Sc W m W' m' mf Ew pos SF); [exact HT | exact Hfr | exact EFa | exact Hsp | lia | |].
- right; right; left. lia.
- intros He. destruct (HE _ He) as [X|X]; [exact (HA (shadow_addr SF + c) ltac:(lia) X) | lia].
Qed.

(* A range of bytes kept from a given state on. *)
Definition d3_kr (lo hi : Z) (W0 : world SEGS) (m0 : word -> option byte) (W' : world SEGS) (m' : word -> option byte) : Prop :=
  forall a, lo <= a < hi -> aview SEGS (w_H W') m' a = aview SEGS (w_H W0) m0 a.
Lemma d3_kr_refl : forall lo hi W m, d3_kr lo hi W m W m.
Proof. intros lo hi W m a _. reflexivity. Qed.
Lemma d3_kr_frame : forall lo hi W0 m0 (W : world SEGS) m m' E (rs : smem),
  d3_kr lo hi W0 m0 W m -> 0 <= lo -> hi <= 2 ^ 64 ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> ~ (lo <= a < hi)) ->
  d3_kr lo hi W0 m0 W m'.
Proof.
intros lo hi W0 m0 W m m' E rs HK H0 H1 HF Hw a Ha. rewrite <- (HK a Ha).
apply (kept_of_frame E rs (w_H W) m m' (fun x => ~ (lo <= x < hi)) HF Hw); lia.
Qed.
Lemma d3_kr_tcj : forall lo hi W0 m0 STK lyc Sc W m W' m' (Ew : Z -> Prop) pos sp SF,
  d3_kr lo hi W0 m0 W m -> tcj_kept B STK lyc Sc W m W' m' sp Ew ->
  frames Sc = [(4, pos)] -> frame_addr lyc 4 pos = SF -> alloc_ceiling <= sp ->
  SF <= lo -> hi <= SF + 1024 -> 0 <= SF -> SF + 1024 <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> ~ Ew a) ->
  d3_kr lo hi W0 m0 W' m'.
Proof.
intros lo hi W0 m0 STK lyc Sc W m W' m' Ew pos sp SF HK HT Hfr EFa Hsp H0 H1 H2 H3 HE a Ha. rewrite <- (HK a Ha).
apply (d3_tcj_keep STK lyc Sc W m W' m' sp Ew pos SF); [exact HT | exact Hfr | exact EFa | exact Hsp | lia | | apply HE; exact Ha].
right; left. lia.
Qed.
Lemma d3_kr_all : forall lo hi W0 m0 (W : world SEGS) m m' xlo xhi,
  d3_kr lo hi W0 m0 W m -> 0 <= lo -> hi <= 2 ^ 64 -> (hi <= xlo \/ xhi <= lo) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (xlo <= a < xhi) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  d3_kr lo hi W0 m0 W m'.
Proof. intros lo hi W0 m0 W m m' xlo xhi HK H0 H1 Hd HA a Ha. rewrite <- (HK a Ha). apply HA; lia. Qed.
Lemma d3_garr8_kr : forall lo W0 m0 W m l,
  d3_kr lo (lo + Z.of_nat (length l)) W0 m0 W m -> garr8 SEGS (rd W0 m0) lo l -> garr8 SEGS (rd W m) lo l.
Proof.
intros lo W0 m0 W m l HK Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS (w_H W0) (w_H W) m0 m (lo + Z.of_nat j) (lo + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros kk Hkk. apply HK. lia.
Qed.

Lemma d3_garr8_kr' : forall lo n W0 m0 W m l, d3_kr lo (lo + n) W0 m0 W m -> Z.of_nat (length l) = n ->
  garr8 SEGS (rd W0 m0) lo l -> garr8 SEGS (rd W m) lo l.
Proof. intros lo n W0 m0 W m l HK Hn Hg. subst n. exact (d3_garr8_kr lo W0 m0 W m l HK Hg). Qed.
Lemma d3_kk_below : forall ly S mf SF W0 m0 W m W' m' lo,
  d3_kk ly S mf SF W0 m0 W m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < mf) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  SF + 1024 <= lo -> shadow_addr SF + 128 <= lo ->
  (forall b sz, In (b, sz) (ablocks B ly S) -> b + req_size sz <= lo) ->
  d3_kk ly S mf SF W0 m0 W' m'.
Proof.
intros ly S mf SF W0 m0 W m W' m' lo HK HA H1 H2 HB.
apply (d3_kk_step ly S mf SF W0 m0 W m W' m' HK). intros a Ha Hc Hw. apply HA; [exact Ha|]. intros Hr.
destruct Hc as [Hc | [Hc | [Hc | (b & sz & Hin & Hb)]]]; try lia. specialize (HB b sz Hin). lia.
Qed.
Lemma d3_kc_below : forall SF W0 m0 W m W' m' lo hi,
  d3_kc SF W0 m0 W m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  0 <= shadow_addr SF -> shadow_addr SF + 128 <= lo -> lo <= 2 ^ 64 ->
  d3_kc SF W0 m0 W' m'.
Proof. intros SF W0 m0 W m W' m' lo hi HK HA H0 H1 H2 c Hc. rewrite <- (HK c Hc). apply HA; lia. Qed.

Lemma d3_add_alias : forall E ss ms a b,
  st_ok_pi SEGS VAL E ss ms -> sv_denot E a = sv_denot E b -> st_ok_pi SEGS VAL E (add_alias ss a b) ms.
Proof. intros E ss ms a b HS H. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_add_alias SEGS E _ ms a b HS H). Qed.

(* The helper for seg_D3, d3_finish (in Section c, right before `Ltac d3_env`, proved below):
   the inv_tail assembly at 0x813b4 from the start boundary (inv_caseV's facts) and the final state of the walk.

   How it goes: the walk's final state differs from the start boundary only inside d3_wr (mf+208..216, `v` and
   `ev` at SF+224..312, `hw` at SF+432..444 and the shadow cells SF's shadow + 28..39), so every byte the
   boundary speaks of -- the machine frame and the entry's saved words above it, the class-4 frame outside `v`,
   `ev` and `hw`, the frame's other shadow cells, the payload copy and the input block -- is carried over by
   d3_kk (KMF / KSF / KSH / KBK below, one per class of d3_cls). `hw`'s new value is the premise's, and the
   model (D3M.ver_hw) says it is what rec_have / rec_hwb hold at S i. The meter follows from HMT0 (mo_le MT S2
   Sf 0) with mo_le_trans / mo_ok_step, the journal and the blocks from the premises, the fds and fs from
   AJ_NIL_IO on the final journal. *)
Lemma d3_finish : forall g pos mf i pl ly2 S2 W2 regs2 mem2 md2 lyf Sf Wf regsf memf mdf,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat i + 3 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat i + 3) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat i + 3)) * (mo_malloc MT 256 + mo_free MT)) ->
  ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  P_body B g pos mf i pl ly2 S2 W2 regs2 mem2 ->
  hw_at g pos i W2 mem2 ->
  SlotModel.rec_r (e_pl g) i = 1 -> SlotModel.rec_addr (e_pl g) i = RcIdentModel.ADDR_REAC_VERSION ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    lyf Sf Wf memf mdf (4 * Z.of_nat i + 3) ->
  frames Sf = [(4, pos)] -> Permutation (ablocks B lyf Sf) (ablocks B ly2 S2) ->
  d3_kk ly2 S2 mf (SFa g pos) W2 mem2 Wf memf ->
  val_mem SEGS (rd Wf memf) (SFa g pos + 432) 4 1 ->
  bytes_at8 Wf memf (SFa g pos + 436) (firstn 8 (SlotModel.rec_pl (e_pl g) i)) ->
  getr regsf 2 = getr regs2 2 -> getr regsf 9 = getr regs2 9 -> getr regsf 8 = getr regs2 8 ->
  getr regsf 3 = getr regs2 3 -> getr regsf 4 = getr regs2 4 -> getr regsf 19 = getr regs2 19 ->
  getr regsf 22 = getr regs2 22 ->
  getr regsf 26 = w64 (e_p g + SlotModel.rec_body (e_pl g) i) -> getr regsf 24 = w64 (SFa g pos + V_before) ->
  getr regsf 25 = w64 pl -> getr regsf 21 = w64 (Z.of_nat i) ->
  inv_tail B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS g pos mf i pl Wf (cfg_at SEGS (BASE + 0xca8) regsf memf mdf).
Proof.
intros g pos mf i pl ly2 S2 W2 regs2 mem2 md2 lyf Sf Wf regsf memf mdf
  HJ2 Hfrs Hkr MLE MOK HEC HPB HHW Hr1 Hav HJf Hfrsf Hperm HKK Hhave Hhwb
  R2 R9 R8 R3 R4 R19 R22 R26 R24 R25 R21.
unfold d3_kk in HKK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
destruct HEC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  Q24 & Q32 & Q40 & Q48 & Q56 & Q64 & Q72 & Q80 & Q88 & Q96 & Q104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
destruct HPB as (Hi & Hbl & Hpl & Hid & V112 & Hfix & Hmid & Hmag & V136 & V144 & V152 & V160 & Rk & Hcur).
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsp47 : e_sp0 g <= 2 ^ 47) by (clear - Hshi H47; lia).
assert (Hmfhi : mf + 320 <= 2 ^ 47) by (clear - Hmfb Hsp47; lia).
assert (Hinpl : In (pl, SlotModel.rec_k (e_pl g) i) (ablocks B ly2 S2)).
{ destruct Hbl as [Hpm _]. apply (Permutation_in _ (Permutation_sym Hpm)). left. reflexivity. }
pose proof (SlotModel.rec_k_range (e_pl g) i) as Hkrange.
assert (Lpl : Z.of_nat (length (SlotModel.rec_pl (e_pl g) i)) = SlotModel.rec_k (e_pl g) i)
  by (rewrite SlotModel.rec_pl_length; clear - Hkrange; lia).
pose proof (req_size_pos (SlotModel.rec_k (e_pl g) i) ltac:(clear - Hkrange; lia)) as [Rq1 Rq2].
assert (Lid : Z.of_nat (length (m_id g (S i))) = 38)
  by (unfold m_id; rewrite SlotModel.rec_id_length; reflexivity).
(* ---- the bytes the walk never wrote, class by class of d3_cls ------------------------------------------- *)
assert (NWmf : forall a, mf <= a -> (a < mf + 208 \/ mf + 216 <= a) -> ~ d3_wr mf (SFa g pos) a).
{ intros a Ha Hb Hw. unfold d3_wr, shadow_addr, SHADOW_OFF in Hw.
  clear - Ha Hb Hw Hmf0 HSF0 HSF1 C1. lia. }
assert (NWsf : forall a, SFa g pos <= a < SFa g pos + 1024 ->
  (a < SFa g pos + 224 \/ SFa g pos + 312 <= a) -> (a < SFa g pos + 432 \/ SFa g pos + 444 <= a) ->
  ~ d3_wr mf (SFa g pos) a).
{ intros a Ha H1 H2 Hw. unfold d3_wr in Hw. destruct Hw as [Hw | [Hw | [Hw | Hw]]].
  - clear - Ha Hw Hmf0 HSF1 C1. lia.
  - clear - Hw H1. lia.
  - clear - Hw H2. lia.
  - apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 a);
    [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp
    | unfold shadow_addr, SHADOW_OFF in Hw; clear - Hw; lia | clear - Ha; lia]. }
assert (NWsh : forall c, 0 <= c < 128 -> (c < 28 \/ 39 <= c) ->
  ~ d3_wr mf (SFa g pos) (shadow_addr (SFa g pos) + c)).
{ intros c Hc Hn Hw. unfold d3_wr in Hw. destruct Hw as [Hw | [Hw | [Hw | Hw]]].
  - unfold shadow_addr, SHADOW_OFF in Hw. clear - Hw Hc Hmf0 HSF0 HSF1 C1. lia.
  - apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 (shadow_addr (SFa g pos) + c));
    [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp
    | unfold shadow_addr, SHADOW_OFF; clear - Hc; lia | clear - Hw; lia].
  - apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 (shadow_addr (SFa g pos) + c));
    [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp
    | unfold shadow_addr, SHADOW_OFF; clear - Hc; lia | clear - Hw; lia].
  - unfold shadow_addr, SHADOW_OFF in Hw. clear - Hw Hn. lia. }
assert (NWbk : forall b m a, In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
  ~ d3_wr mf (SFa g pos) a).
{ intros b m a Hin Ha Hw.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin) as (_ & Hb0 & Hbc & Hbapp & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 b m 4 pos HAR2 Hin Hin4) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFa, HFB in Hd.
  unfold d3_wr in Hw. destruct Hw as [Hw | [Hw | [Hw | Hw]]].
  - clear - Ha Hw Hbc Hmf0 C1. lia.
  - clear - Ha Hw Hd. lia.
  - clear - Ha Hw Hd. lia.
  - apply (fshadow_not_app (SFa g pos) 128 b (req_size m) a);
    [exact HSF0 | clear - HSF1 C1; lia | exact Hbapp
    | unfold shadow_addr, SHADOW_OFF in Hw; clear - Hw; lia | exact Ha]. }
assert (KMF : forall a, mf <= a -> (a < mf + 208 \/ mf + 216 <= a) -> a < 2 ^ 64 ->
  aview SEGS (w_H Wf) memf a = aview SEGS (w_H W2) mem2 a).
{ intros a H1 H2 H3. apply HKK;
  [clear - H1 H3 Hmf0 C1; lia | unfold d3_cls; left; exact H1 | exact (NWmf a H1 H2)]. }
assert (KSF : forall a, SFa g pos <= a < SFa g pos + 1024 ->
  (a < SFa g pos + 224 \/ SFa g pos + 312 <= a) -> (a < SFa g pos + 432 \/ SFa g pos + 444 <= a) ->
  aview SEGS (w_H Wf) memf a = aview SEGS (w_H W2) mem2 a).
{ intros a H1 H2 H3. apply HKK;
  [clear - H1 HSF0 HSF1 C1; lia | unfold d3_cls; right; left; exact H1 | exact (NWsf a H1 H2 H3)]. }
assert (KSH : forall c, 0 <= c < 128 -> (c < 28 \/ 39 <= c) ->
  aview SEGS (w_H Wf) memf (shadow_addr (SFa g pos) + c)
  = aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos) + c)).
{ intros c H1 H2. apply HKK;
  [unfold shadow_addr, SHADOW_OFF; clear - H1 HSF0 HSF1 C1; lia
  | unfold d3_cls; right; right; left; clear - H1; lia | exact (NWsh c H1 H2)]. }
assert (KBK : forall b m a, In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
  aview SEGS (w_H Wf) memf a = aview SEGS (w_H W2) mem2 a).
{ intros b m a Hin Ha.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin) as (_ & Hb0 & Hbc & _ & _).
  apply HKK;
  [clear - Ha Hb0 Hbc C1; lia
  | unfold d3_cls; right; right; right; exists b, m; split; [exact Hin | exact Ha]
  | exact (NWbk b m a Hin Ha)]. }
(* ---- the same, as facts of memory ------------------------------------------------------------------------ *)
assert (VMV : forall a (n : nat) v,
  (forall c, 0 <= c < Z.of_nat n -> aview SEGS (w_H Wf) memf (a + c) = aview SEGS (w_H W2) mem2 (a + c)) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd Wf memf) a n v)
  by (intros a n v Hk Hv; exact (val_mem_moved SEGS (w_H W2) (w_H Wf) mem2 memf a a n v Hk Hv)).
assert (GAR : forall a l,
  (forall c, 0 <= c < Z.of_nat (length l) -> aview SEGS (w_H Wf) memf (a + c) = aview SEGS (w_H W2) mem2 (a + c)) ->
  garr8 SEGS (rd W2 mem2) a l -> garr8 SEGS (rd Wf memf) a l).
{ intros a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (val_mem_moved SEGS (w_H W2) (w_H Wf) mem2 memf (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0));
  [|exact Hv].
  intros c Hc. replace (a + Z.of_nat j + c) with (a + (Z.of_nat j + c)) by (clear; lia).
  apply Hk. clear - Hj Hc. lia. }
assert (VH : forall off (n : nat) v, 0 <= off -> (off + Z.of_nat n <= 208 \/ 216 <= off) ->
  mf + off + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (rd W2 mem2) (mf + off) n v -> val_mem SEGS (rd Wf memf) (mf + off) n v).
{ intros off n v H0 H1 H2 Hv. apply (VMV _ n v); [|exact Hv].
  intros c Hc. apply KMF; [clear - H0 Hc; lia | clear - H0 H1 Hc; lia | clear - H2 Hc; lia]. }
assert (VS : forall off v, 8 <= off <= 104 ->
  val_mem SEGS (rd W2 mem2) (e_sp0 g - off) 8 v -> val_mem SEGS (rd Wf memf) (e_sp0 g - off) 8 v).
{ intros off v H0 Hv.
  assert (Eo : e_sp0 g - off = mf + (e_sp0 g - off - mf)) by (clear; lia).
  rewrite Eo in Hv |- *.
  apply (VH (e_sp0 g - off - mf) 8%nat v);
  [clear - H0 Hmfb; lia | right; clear - H0 Hmfb; lia | clear - H0 Hmfb Hsp47; lia | exact Hv]. }
assert (VF : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= 1024 ->
  (off + Z.of_nat n <= 224 \/ 312 <= off) -> (off + Z.of_nat n <= 432 \/ 444 <= off) ->
  val_mem SEGS (rd W2 mem2) (SFa g pos + off) n v -> val_mem SEGS (rd Wf memf) (SFa g pos + off) n v).
{ intros off n v H0 H1 H2 H3 Hv. apply (VMV _ n v); [|exact Hv].
  intros c Hc. apply KSF; [clear - H0 H1 Hc; lia | clear - H0 H2 Hc; lia | clear - H0 H3 Hc; lia]. }
assert (BF : forall off bs, 0 <= off -> off + Z.of_nat (length bs) <= 1024 ->
  (off + Z.of_nat (length bs) <= 224 \/ 312 <= off) -> (off + Z.of_nat (length bs) <= 432 \/ 444 <= off) ->
  bytes_at8 W2 mem2 (SFa g pos + off) bs -> bytes_at8 Wf memf (SFa g pos + off) bs).
{ intros off bs H0 H1 H2 H3 Hb. unfold bytes_at8 in *.
  apply (GAR (SFa g pos + off) (map (fun b : byte => bv_unsigned b) bs)); [|exact Hb].
  intros c Hc. rewrite length_map in Hc.
  apply KSF; [clear - H0 H1 Hc; lia | clear - H0 H2 Hc; lia | clear - H0 H3 Hc; lia]. }
assert (BB : forall b m a bs, In (b, m) (ablocks B ly2 S2) -> b <= a ->
  a + Z.of_nat (length bs) <= b + req_size m ->
  bytes_at8 W2 mem2 a bs -> bytes_at8 Wf memf a bs).
{ intros b m a bs Hin H1 H2 Hb. unfold bytes_at8 in *.
  apply (GAR a (map (fun b0 : byte => bv_unsigned b0) bs)); [|exact Hb].
  intros c Hc. rewrite length_map in Hc. apply (KBK b m); [exact Hin | clear - H1 H2 Hc; lia]. }
assert (SZF : forall off n, 0 <= off -> 0 <= n -> off + n <= 1024 -> (off + n <= 224 \/ 312 <= off) ->
  sh_zero W2 mem2 (SFa g pos + off) n -> sh_zero Wf memf (SFa g pos + off) n).
{ intros off n H0 Hn H1 H2 Hz c Hc. unfold sh_zero, zero_shadow in Hz |- *.
  assert (Ec : shadow_of_addr SHADOW_OFF (SFa g pos + off) + c = shadow_addr (SFa g pos) + (off / 8 + c))
    by (unfold shadow_of_addr, shadow_addr; clear - H0 H1 HSF64; lia).
  rewrite Ec, KSH;
  [rewrite <- Ec; exact (Hz c Hc) | clear - H0 Hn H1 Hc; lia | clear - H0 Hn H1 H2 Hc; lia]. }
assert (SBF : forall off n, 0 <= off -> 0 <= n -> off + n <= 1024 -> (off + n <= 224 \/ 312 <= off) ->
  sh_blk W2 mem2 (SFa g pos + off) n -> sh_blk Wf memf (SFa g pos + off) n).
{ intros off n H0 Hn H1 H2 Hb. unfold sh_blk in *.
  apply (block_shadow_agree (aview SEGS (w_H W2) mem2)); [|exact Hb].
  intros c Hc.
  assert (Ec : shadow_of_addr SHADOW_OFF (SFa g pos + off) + c = shadow_addr (SFa g pos) + (off / 8 + c))
    by (unfold shadow_of_addr, shadow_addr; clear - H0 H1 HSF64; lia).
  rewrite Ec. apply KSH; [clear - H0 Hn H1 Hc; lia | clear - H0 Hn H1 H2 Hc; lia]. }
(* the input block the contract gave: a block of the start state, outside d3_wr *)
assert (HINB : bytes_at8 Wf memf (e_p g) (e_pl g)).
{ destruct Hinp as [[Hn0 _] | [Hn0 Hine]].
  - assert (Enil : e_pl g = []).
    { rewrite Hn0 in Hlen. destruct (e_pl g) as [|x l]; [reflexivity | cbn in Hlen; clear - Hlen; lia]. }
    rewrite Enil. unfold bytes_at8. intros j Hj. exfalso. cbn in Hj. clear - Hj. lia.
  - assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
    { destruct Hbl as [Hpm _]. apply (Permutation_in _ (Permutation_sym Hpm)). right. exact Hine. }
    pose proof (req_size_pos (e_n g) ltac:(clear - Hn0; lia)) as [P1 P2].
    apply (BB (e_p g) (e_n g) (e_p g) (e_pl g) Hine2);
    [clear; lia | clear - Hlen P2; lia | exact Hinb]. }
(* the model's hardware block after the record, and the two io facts of the final journal *)
destruct (D3M.ver_hw (e_pl g) i Hr1 Hav) as (Hhv & Hhb).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJf) as [Efd Efs].
(* ---- the boundary -------------------------------------------------------------------------------------- *)
unfold inv_tail, acut.
exists lyf, Sf, regsf, memf, mdf.
split; [reflexivity|].
split; [exact HJf|].
split; [exact Hfrsf|].
split; [exact Hkr|].
split.
{ pose proof (mo_le_trans MT MTL _ _ _ _ _ MLE (HMT0 S2 Sf)) as HL.
  rewrite Z.add_0_r in HL. exact HL. }
split.
{ apply (mo_ok_step MT MTL S2 Sf 0); [rewrite Z.add_0_l; exact MOK | exact (HMT0 S2 Sf)]. }
split.
{ unfold ecommon.
  split; [rewrite R2; exact Rsp|].
  split; [rewrite R9; exact Rs1|].
  split; [rewrite R8; exact Rs0|].
  split; [exact Hmfb|].
  split; [exact Hmf32|].
  split; [rewrite R3; exact Rgp|].
  split; [rewrite R4; exact Rtp|].
  split; [rewrite R19; exact Rs3|].
  split; [apply (VH 80 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact V80]|].
  split; [apply (VH 192 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact V192]|].
  split; [apply (VH 176 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact V176]|].
  split; [apply (VS 8); [clear; lia | exact Vra]|].
  split; [apply (VS 16); [clear; lia | exact Vs0]|].
  split; [apply (VS 24); [clear; lia | exact Q24]|].
  split; [apply (VS 32); [clear; lia | exact Q32]|].
  split; [apply (VS 40); [clear; lia | exact Q40]|].
  split; [apply (VS 48); [clear; lia | exact Q48]|].
  split; [apply (VS 56); [clear; lia | exact Q56]|].
  split; [apply (VS 64); [clear; lia | exact Q64]|].
  split; [apply (VS 72); [clear; lia | exact Q72]|].
  split; [apply (VS 80); [clear; lia | exact Q80]|].
  split; [apply (VS 88); [clear; lia | exact Q88]|].
  split; [apply (VS 96); [clear; lia | exact Q96]|].
  split; [apply (VS 104); [clear; lia | exact Q104]|].
  split; [apply (VH 24 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact Vmf24]|].
  split; [apply (VF 1016 8%nat);
    [clear; lia | clear; lia | right; clear; lia | right; clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  exact HINB. }
split.
{ unfold P_body.
  split; [exact Hi|].
  split; [destruct Hbl as [Hpm Hfa]; split; [exact (Permutation_trans Hperm Hpm) | exact Hfa]|].
  split; [apply (BB pl (SlotModel.rec_k (e_pl g) i) pl (SlotModel.rec_pl (e_pl g) i) Hinpl);
    [clear; lia | clear - Lpl Rq2; lia | exact Hpl]|].
  split.
  { destruct Hid as (Hidb & Hidz & Hidk). unfold V_id, N_id in Hidb, Hidz, Hidk.
    unfold id_at, V_id, N_id.
    split; [apply (BF 352 (m_id g (S i)));
      [clear; lia | clear - Lid; lia | right; clear; lia | left; clear - Lid; lia | exact Hidb]|].
    split; [apply (SZF 352 38); [clear; lia | clear; lia | clear; lia | right; clear; lia | exact Hidz]|].
    apply (SBF 352 38); [clear; lia | clear; lia | clear; lia | right; clear; lia | exact Hidk]. }
  split; [apply (VH 112 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact V112]|].
  split.
  { destruct Hfix as (F32 & F40 & F48 & F72 & F88 & F96 & F104 & F120 & F128). unfold mf_fixed.
    split; [apply (VH 32 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact F32]|].
    split; [apply (VH 40 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact F40]|].
    split; [apply (VH 48 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact F48]|].
    split; [apply (VH 72 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact F72]|].
    split; [apply (VH 88 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact F88]|].
    split; [apply (VH 96 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact F96]|].
    split; [apply (VH 104 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact F104]|].
    split; [apply (VH 120 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact F120]|].
    apply (VH 128 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact F128]. }
  split; [unfold mf_id in Hmid |- *;
    apply (VH 184 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact Hmid]|].
  split; [unfold mf_again in Hmag |- *;
    apply (VH 168 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact Hmag]|].
  split; [apply (VH 136 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact V136]|].
  split; [apply (VH 144 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact V144]|].
  split; [apply (VH 152 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact V152]|].
  split; [apply (VH 160 8%nat); [clear; lia | left; clear; lia | clear - Hmfhi; lia | exact V160]|].
  split; [rewrite R22; exact Rk|].
  exact Hcur. }
split.
{ destruct HHW as (_ & _ & Hhz & Hhk). unfold V_hw, N_hw in Hhz, Hhk.
  unfold hw_at, V_hw, N_hw.
  split; [unfold m_have; rewrite Hhv; exact Hhave|].
  split; [unfold m_hwb; rewrite Hhb;
    replace (SFa g pos + 432 + 4) with (SFa g pos + 436) by (clear; lia); exact Hhwb|].
  split; [apply (SZF 432 12); [clear; lia | clear; lia | clear; lia | right; clear; lia | exact Hhz]|].
  apply (SBF 432 12); [clear; lia | clear; lia | clear; lia | right; clear; lia | exact Hhk]. }
split; [exact R26|].
split; [exact R24|].
split; [exact R25|].
exact R21.
Qed.

Ltac d3_env := repeat first [ rewrite ew_ewset_other by (apply Nat.eqb_neq; reflexivity)
                            | rewrite ew_havoc_old by (apply Nat.ltb_lt; reflexivity) ].
(* lia in a leaf goal, after dropping the word / env facts it cannot use (their terms are large). *)
Ltac d3_slim := repeat match goal with
  | H : bv_unsigned _ = _ |- _ => clear H
  | H : ew _ _ = _ |- _ => clear H
  | H : getr _ _ = _ |- _ => clear H
  | H : spZ _ = _ |- _ => clear H
  end.

Ltac d3_envh H := repeat first [ rewrite ew_ewset_other in H by (apply Nat.eqb_neq; reflexivity)
                               | rewrite ew_havoc_old in H by (apply Nat.ltb_lt; reflexivity) ].

Ltac d3_rs := lazymatch goal with |- awr_ok ?E ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' a1 a2 a3 a4 a5 a6 a7) end.
Ltac d3_ro := apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|].
Ltac d3_in := repeat (first [left; reflexivity | right]).
Ltac d3_be16 G1 G2 Gr Heq n1 n2 nr j1 j2 RB :=
  exfalso; lazymatch goal with Hc : branch_taken _ (sv_denot ?Ev _) _ = false |- _ =>
  let Ht := fresh "Ht" in
  pose proof (d3_be16_taken Ev n1 n2 nr _ _ ltac:(d3_env; exact G1) ltac:(d3_env; exact G2)
    ltac:(d3_env; rewrite Gr; f_equal; exact Heq) (RB j1) (RB j2)) as Ht;
  rewrite Ht in Hc; discriminate Hc end.

Ltac d3_win rw :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb wlo whi aa Hin Hr; try unfold d3_ss0 in Hin; unfold windows in Hin; vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val] in Hr;
      first [ exfalso; clear - Hr; lia | d3_envh Hr; rw Hr; try unfold d3_wr; d3_slim; lia ] | ]);
  destruct Hin.
Ltac d3_kkr rw := repeat match goal with
  | HKK : d3_kk _ _ _ _ _ _ _ ?m1, HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    let H' := fresh "HKK" in
    pose proof (d3_kk_frame _ _ _ _ _ _ _ m1 m2 Ex rs HKK HFr ltac:(d3_win rw)) as H'; clear HKK; rename H' into HKK
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Ltac d3_kcr mf HSHA rw := repeat match goal with
  | HKC : d3_kc _ _ _ _ ?m1, HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    let H' := fresh "HKC" in
    pose proof (d3_kc_frame _ mf _ _ _ m1 m2 Ex rs HKC HSHA HFr ltac:(d3_win rw)) as H'; clear HKC; rename H' into HKC
  end.
Ltac d3_krr rw := repeat match goal with
  | HK : d3_kr ?lo ?hi ?W0 ?m0 ?W ?m1, HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    let H' := fresh "KR" in
    pose proof (d3_kr_frame lo hi W0 m0 W m1 m2 Ex rs HK ltac:(d3_slim; lia) ltac:(d3_slim; lia) HFr ltac:(d3_win rw)) as H'; clear HK;
    rename H' into HK
  end.

Ltac d3_norm H :=
  cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add map CLOB] in H;
  repeat (rewrite ew_havoc_old in H; [|cbv; lia]);
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in H.

Ltac d3_xlia := d3_slim; first [ lia | unfold d3_apart in *; lia
  | unfold d3_apart, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia ].
Ltac d3_clearU E0 := repeat match goal with
  | H : bv_unsigned (ew ?E _) = _ |- _ => tryif constr_eq E E0 then fail else clear H
  end.

Theorem seg_D3_holds :
  seg_D3 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS.
Proof.
intros g pos mf i pl W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
pose proof HJ as HJs.
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  Q24 & Q32 & Q40 & Q48 & Q56 & Q64 & Q72 & Q80 & Q88 & Q96 & Q104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof HP as ((Hi & Hbl & Hpl & Hid & V112 & Hfix & Hmid & Hmag & V136 & V144 & V152 & V160 & Rk & Hcur) &
  Hhw & Hr1 & Hav & R25 & R14 & R10 & R11 & R18 & R26 & R24 & R20).
pose proof Hfix as (F32 & F40 & F48 & F72 & F88 & F96 & F104 & F120 & F128).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres2 & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
assert (Hsh1 : 0x7fff8000 + 512 <= sh /\ sh + 128 <= 0x7fff8000 + 2 ^ 44).
{ rewrite Esh. unfold SHADOW_OFF in *. clear - HSF0 HSF1 C1. lia. }
assert (Hnev : st_nev S2 <= EV_MAX) by (clear - Hnev2 Hnev0 Hk HEV; unfold EV_LLVMF in *; lia).
(* ---- the model ---- *)
set (inp := e_pl g) in *.
set (k := SlotModel.rec_k inp i) in *.
set (plb := SlotModel.rec_pl inp i) in *.
assert (Hi64 : (Z.of_nat i < 64)%Z).
{ unfold m_nrec, SlotModel.nrecn in Hi. fold inp in Hi. pose proof (SlotModel.nrec_range inp) as Hnr. clear - Hi Hnr. lia. }
pose proof (D3M.ver_k8 inp i Hr1 Hav) as Hk8. fold k in Hk8.
pose proof (SlotModel.rec_pl_length inp i) as Hplen. fold plb k in Hplen.
pose proof (SlotModel.rec_k_range inp i) as Hkr. fold k in Hkr.
destruct (D3M.ver_id inp i Hr1 Hav) as (Hmaj & Hmin & Hpat). fold plb in Hmaj, Hmin, Hpat.
destruct (D3M.ver_hw inp i Hr1 Hav) as (Hhv & Hhb). fold plb in Hhb.
unfold m_id in R18, R26, R24. fold inp in R18, R26, R24.
set (idS := SlotModel.rec_id inp (S i)) in *.
destruct (D3M.mmp_range idS) as (Rma & Rmi & Rpa).
set (maj := RcIdentModel.major idS) in *. set (mnr := RcIdentModel.minor idS) in *.
set (pat := RcIdentModel.patch idS) in *.
pose proof (fun j : nat => SlotModel.bz_range (RcIdentModel.nthb plb j)) as RB.
assert (VB : forall j, (j < 8)%nat ->
  val_mem SEGS (rd W2 mem2) (pl + Z.of_nat j) 1 (RcIdentModel.bz (RcIdentModel.nthb plb j))).
{ intros j Hj. apply (d3_garr8_byte _ pl plb j Hpl). lia. }
assert (Hinpl : In (pl, k) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl k HAR2 Hinpl) as (Hpl16 & Hpl4096 & Hplce & Hplapp & _).
pose proof (req_size_pos k ltac:(lia)) as [Rq1 Rq2].
set (BODY := e_p g + SlotModel.rec_body inp i) in *.
(* ---- the symbolic state at 0x80f20 ---- *)
pose proof (d3_entry W2 regs2 mem2 mf pl SF BODY (Z.of_nat i) plb Rs1 R20 R25 R14 R10 R11
  ltac:(lia) Hmf32 HSF0 ltac:(lia) HSF64 Hpl4096 ltac:(lia) ltac:(lia) ltac:(clear - Hpl16; lia) ltac:(clear - Hi64; lia)
  F32 F48 F72 F88 V136 V152 V160 V176 VB ltac:(intros o Ho; apply Hpres2; lia)) as HS.
remember (d3_E regs2 plb BODY (Z.of_nat i)) as E0 eqn:HE0.
assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E0 n = ew (Ereg regs2 (d3_extra plb BODY (Z.of_nat i))) n)
  by (intros n Hn; rewrite HE0; unfold d3_E; apply Eimg_low; exact Hn).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs2 r)
  by (intros n r Hn; rewrite EL by (pose proof (u5_range r); unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ n r Hn)).
assert (EX : forall j, (j < 10)%nat -> ew E0 (32 + j) = nth j (d3_extra plb BODY (Z.of_nat i)) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ j)).
assert (AGE : env_agree 32 (Ereg regs2 (d3_extra plb BODY (Z.of_nat i))) E0)
  by (rewrite HE0; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (G2 : ew E0 2 = Z_to_bv 64 mf) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
assert (G3 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Rgp).
assert (G4 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Rtp).
assert (G8 : ew E0 8 = Z_to_bv 64 sp0) by (rewrite (EE 8%nat 8%bv eq_refl); exact Rs0).
assert (G9 : ew E0 9 = Z_to_bv 64 mf) by (rewrite (EE 9%nat 9%bv eq_refl); exact Rs1).
assert (G14 : ew E0 14 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 14%nat 14%bv eq_refl); exact R14).
assert (G18 : ew E0 18 = Z_to_bv 64 maj) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (G19 : ew E0 19 = Z_to_bv 64 sh) by (rewrite (EE 19%nat 19%bv eq_refl); exact Rs3).
assert (G20 : ew E0 20 = Z_to_bv 64 (SF + 288)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (G22 : ew E0 22 = Z_to_bv 64 k) by (rewrite (EE 22%nat 22%bv eq_refl); exact Rk).
assert (G24 : ew E0 24 = Z_to_bv 64 pat) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (G25 : ew E0 25 = Z_to_bv 64 pl) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (G26 : ew E0 26 = Z_to_bv 64 mnr) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (G40 : ew E0 40 = Z_to_bv 64 BODY) by exact (EX 8%nat ltac:(lia)).
assert (G41 : ew E0 41 = Z_to_bv 64 (Z.of_nat i)) by exact (EX 9%nat ltac:(lia)).
assert (GB : forall j, (j < 8)%nat -> ew E0 (32 + j) = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb plb j))).
{ intros j Hj. rewrite (EX j ltac:(lia)). unfold d3_extra. do 8 (destruct j as [|j]; [reflexivity|]). lia. }
pose proof (GB 0%nat ltac:(lia)) as G32. pose proof (GB 1%nat ltac:(lia)) as G33.
pose proof (GB 2%nat ltac:(lia)) as G34. pose proof (GB 3%nat ltac:(lia)) as G35.
pose proof (GB 4%nat ltac:(lia)) as G36. pose proof (GB 5%nat ltac:(lia)) as G37.
pose proof (GB 6%nat ltac:(lia)) as G38. pose proof (GB 7%nat ltac:(lia)) as G39.
cbn [Nat.add] in G32, G33, G34, G35, G36, G37, G38, G39.
clear HE0 EL EX GB.
assert (U9 : bv_unsigned (ew E0 9) = mf) by (rewrite G9; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS d3_Bx d3_SH0 E0 (rd W2 mem2)).
{ unfold sh_ok, d3_SH0. constructor; [|constructor].
  apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E0 d3_Bx 25 pl k 0 8 HAR2 Hinpl).
  - unfold d3_Bx. apply (U_atom E0 14 SHADOW_OFF G14). unfold SHADOW_OFF. lia.
  - apply (U_atom E0 25 pl G25). lia.
  - lia.
  - lia. }
assert (U19 : bv_unsigned (ew E0 19) = sh) by (rewrite G19; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (U20 : bv_unsigned (ew E0 20) = SF + 288) by (rewrite G20; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E0 25) = pl) by (rewrite G25; apply unsigned_lit_small; lia).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 pl k 4 pos HAR2 Hinpl Hin4) as Hdf0.
unfold zdisjoint in Hdf0. cbn [fst snd] in Hdf0. rewrite EFa, HFB in Hdf0.
(* The disjunctive facts stay out of lia's context (a disjunction doubles every lia after it): each is kept
   behind d3_apart / d3_shapart and opened only where a goal needs it. *)
assert (HDF : d3_apart pl (req_size k) SF 1024) by exact Hdf0. clear Hdf0.
assert (HPLS : d3_apart pl 8 sh 128).
{ pose proof Hplapp as X. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in X. unfold d3_apart.
  clear - X Esh Hsh1 Rq1 HSF0 HSF1. unfold SHADOW_OFF in *. lia. }
assert (HSFS : d3_apart sh 128 SF 1024).
{ pose proof HSFapp as X. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in X. unfold d3_apart.
  clear - X Esh Hsh1 HSF0 HSF1. unfold SHADOW_OFF in *. lia. }
assert (HSHA : d3_shapart SF mf).
{ unfold d3_shapart. change (shadow_addr SF) with sh. split; [|split; [lia | split; lia]].
  intros a Ha Hb. pose proof HSFapp as X. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in X.
  change (shadow_addr SF) with sh in Ha. clear - X Ha Hb Esh Hsh1 HSF0 HSF1. unfold SHADOW_OFF in *. lia. }
pose proof (d3_kk_refl ly2 S2 mf SF W2 mem2) as HKK.
unfold cfg_at. change (w64 (BASE + 0x814)) with (Z_to_bv 64 (BASE + 0x814)).
(* ---- run 1: the shadow checks of pl[2], pl[3] and the first halfword check (0x80f4c) ---- *)
paj_run_tok RUN HS HJ SHOK d3_Bspan.
{ unfold d3_ss0. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0)); [reflexivity | rewrite U9; ring | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
d3_kkr ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H).
psrr_branch_tok RUN BR HS SHOK d3_Bspan.
2: { d3_be16 G34 G35 G18 Hmaj 34%nat 35%nat 18%nat 2%nat 3%nat RB. }
clear Hc.
(* ---- run 2: pl[4], pl[5] and the second halfword check (0x80f8c) ---- *)
paj_run_tok RUN HS HJ SHOK d3_Bspan.
{ d3_rs. d3_ro.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0)); [reflexivity | d3_env; rewrite U9; ring | cbn; lia | cbn; lia |].
  d3_ro. apply awr_ok_nil. }
d3_kkr ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H).
psrr_branch_tok RUN BR HS SHOK d3_Bspan.
2: { d3_be16 G36 G37 G26 Hmin 36%nat 37%nat 26%nat 4%nat 5%nat RB. }
clear Hc.
(* ---- run 3: pl[6], pl[7] and the third halfword check (0x80fcc) ---- *)
paj_run_tok RUN HS HJ SHOK d3_Bspan.
{ d3_rs. d3_ro.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0)); [reflexivity | d3_env; rewrite U9; ring | cbn; lia | cbn; lia |].
  d3_ro. apply awr_ok_nil. }
d3_kkr ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H).
psrr_branch_tok RUN BR HS SHOK d3_Bspan.
2: { d3_be16 G38 G39 G24 Hpat 38%nat 39%nat 24%nat 6%nat 7%nat RB. }
clear Hc.
(* ---- run 4: to the first shadow store (0x80fd4), where the token engine stops ---- *)
paj_run_tok RUN HS HJ SHOK d3_Bspan.
{ d3_rs. d3_ro.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0)); [reflexivity | d3_env; rewrite U9; ring | cbn; lia | cbn; lia |].
  d3_ro. apply awr_ok_nil. }
d3_kkr ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H).
(* ---- the shadow cells of v and ev become a writable region; run 5, a plain run to put_dec (0x81008) ---- *)
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => assert (U19x : bv_unsigned (ew Ex 19) = sh) by (d3_env; exact U19) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => assert (U9x : bv_unsigned (ew Ex 9) = mf) by (d3_env; exact U9) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => assert (U25x : bv_unsigned (ew Ex 25) = pl) by (d3_env; exact U25) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
  assert (HSa : st_ok_pi SEGS VAL Ex (mkSS (ss_pc ssx) (ss_regs ssx) (d3_sh :: ss_mem ssx) (ss_resv ssx) (ss_facts ssx))
    (restrict (w_H W2) msx)) end.
{ apply st_ok_pi_add_region; [exact HS | reflexivity | |].
  - unfold region_ok, d3_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19x. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. cbn [restrict ms_mem]. apply (apresent_writable SEGS).
    apply (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sh + o) HJ ltac:(
      right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
      unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; change (1024 / 8) with 128; fold sh; lia))).
  - cbn [ss_mem all_disjoint]. repeat split; (eapply d3_ext; [exact U19x | first [exact U9x | exact U25x] |]); d3_xlia. }
clear HS. rename HSa into HS.
paj_run_shc RUNP RUNC HS HJ.
{ d3_rs.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat sh); [reflexivity | exact U19x | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
    right. unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; change (1024 / 8) with 128; fold sh; lia. }
  d3_ro.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0)); [reflexivity | rewrite U9x; ring | cbn; lia | cbn; lia |].
  d3_ro. apply awr_ok_nil. }
d3_kkr ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H).
(* the facts run 5 stored: mf+208 = 0 and the six shadow cells *)
lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HMO; cbn [ss_mem setpc ms_mem restrict] in HMO;
  pose proof (d3_chunk_val Ex _ _ 9 208 216 208 216 _ 208 8 (SLit 0) 0 HMO ltac:(d3_in) ltac:(d3_in) eq_refl ltac:(lia))
    as V208;
  pose proof (d3_chunk_val Ex _ _ 19 28 39 28 39 _ 28 1 (SLit 0) 0 HMO ltac:(d3_in) ltac:(d3_in) eq_refl ltac:(lia)) as Z28;
  pose proof (d3_chunk_val Ex _ _ 19 28 39 28 39 _ 29 1 (SLit 0) 0 HMO ltac:(d3_in) ltac:(d3_in) eq_refl ltac:(lia)) as Z29;
  pose proof (d3_chunk_val Ex _ _ 19 28 39 28 39 _ 30 1 (SLit 4) 4 HMO ltac:(d3_in) ltac:(d3_in) eq_refl ltac:(lia)) as Z30;
  pose proof (d3_chunk_val Ex _ _ 19 28 39 28 39 _ 36 1 (SLit 0) 0 HMO ltac:(d3_in) ltac:(d3_in) eq_refl ltac:(lia)) as Z36;
  pose proof (d3_chunk_val Ex _ _ 19 28 39 28 39 _ 37 1 (SLit 0) 0 HMO ltac:(d3_in) ltac:(d3_in) eq_refl ltac:(lia)) as Z37;
  pose proof (d3_chunk_val Ex _ _ 19 28 39 28 39 _ 38 1 (SLit 0) 0 HMO ltac:(d3_in) ltac:(d3_in) eq_refl ltac:(lia)) as Z38;
  rewrite U9x in V208; rewrite U19x in Z28, Z29, Z30, Z36, Z37, Z38;
  apply d3_aview_of_vm1 in Z28; [|lia]; apply d3_aview_of_vm1 in Z29; [|lia]; apply d3_aview_of_vm1 in Z30; [|lia];
  apply d3_aview_of_vm1 in Z36; [|lia]; apply d3_aview_of_vm1 in Z37; [|lia]; apply d3_aview_of_vm1 in Z38; [|lia];
  clear HMO end.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (13%bv : bv 5) Ra3;
  prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp1; prreg HS (3%bv : bv 5) Rgp1; prreg HS (4%bv : bv 5) Rtp1 end.
rewrite G20 in Ra0. rewrite U9 in Ra1. rewrite G18 in Ra2. rewrite G2 in Rsp1. rewrite G3 in Rgp1. rewrite G4 in Rtp1.
pose proof (d3_dl1 maj Rma) as Hdl1.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  assert (Usp1 : spZ (ms_regs msx) = mf) by (unfold spZ; rewrite Rsp1; apply unsigned_lit_small; lia);
  assert (Hevz1 : forall j, 0 <= j < 3 -> aview SEGS (w_H W2) (ms_mem msx) (shadow_addr SF + 36 + j) = Some 0)
    by (intros j Hj; change (shadow_addr SF) with sh;
        assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia;
        destruct Hj3 as [-> | [-> | ->]];
        [rewrite Z.add_0_r; exact Z36 | replace (sh + 36 + 1) with (sh + 37) by lia; exact Z37
        | replace (sh + 36 + 2) with (sh + 38) by lia; exact Z38]) end.
d3_clearU E0.
pmkst HS.
(* ---- put_dec(ev, &en, major, 1), 0x81008 ---- *)
eapply SRr_bind.
{ apply (d3_putdec g pos mf W2 _ _ _ ly2 S2 (4 * Z.of_nat i + 3) 0 maj 1 2304 HJ Hfrs Hnev Hmfb Hmf32 Hmf0 HSF0
    ltac:(lia) HSFapp HSF64 Ra0 Ra1 Ra2 Ra3 Rra
    ltac:(lia) eq_refl Rsp1 Rgp1 Rtp1 Rma ltac:(lia) ltac:(lia) ltac:(lia) V208 Hevz1). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfr3 & Hbl3 & HK3 & HG3 & HV3).
rewrite Usp1 in HK3.
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
  let K := eval vm_compute in (run_K A_LIM d3_Bx [] ssx) in
  jafter_call_keep_hi HS K regs3 (mrestrict (w_H W3) mem3) HP3 [1;3]%nat HS3 end.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
  - eapply d3_rk_ro; [d3_env; exact U9 |]. intros a Ha.
    apply (d3_tcj_keep _ _ _ _ _ _ _ mf _ pos SF a HK3 Hfrs EFa ltac:(lia) ltac:(lia)); [left; lia | cbn beta; lia].
  - eapply d3_rk_ro; [d3_env; exact U25 |]. intros a Ha.
    apply (d3_tcj_keep _ _ _ _ _ _ _ mf _ pos SF a HK3 Hfrs EFa ltac:(lia) ltac:(lia));
      [right; right; right; exists pl, k; split; [exact Hinpl | lia] | cbn beta; d3_xlia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS. rewrite Rra.
(* ---- back at 0x8100c: what put_dec #1 left ---- *)
unfold EV_PUT_DEC in HJ3. rewrite Z.add_0_r in HJ3. rewrite Hfrs in Hfr3.
assert (EFa3 : frame_addr ly3 4 pos = SF).
{ pose proof HJ3 as (_ & Hly3 & _). destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  unfold SF, SFa, frame_addr. rewrite EF3. reflexivity. }
pose proof (d3_kk_tcj ly2 S2 mf SF W2 mem2 _ ly2 S2 W2 _ W3 mem3 _ pos HKK HK3 Hfrs EFa ltac:(lia)
  (Permutation_refl _) ltac:(intros a Ha; cbn beta in Ha; unfold d3_wr; d3_slim; lia)) as HKK3.
clear HKK. rename HKK3 into HKK.
assert (CK3 : forall c v, 28 <= c < 39 -> aview SEGS (w_H W2) (ms_mem ms0) (sh + c) = Some v ->
  aview SEGS (w_H W3) mem3 (sh + c) = Some v).
{ intros c v Hcc Hv. rewrite (d3_tcj_keep _ _ _ _ _ _ _ mf _ pos SF (sh + c) HK3 Hfrs EFa ltac:(lia) ltac:(lia)
    ltac:(right; right; left; change (shadow_addr SF) with sh; lia)
    ltac:(cbn beta; intros [X|X]; [lia | exact (proj1 HSHA (sh + c) ltac:(lia) ltac:(lia))])). exact Hv. }
apply CK3 in Z28; [|lia]. apply CK3 in Z29; [|lia]. apply CK3 in Z30; [|lia].
apply CK3 in Z36; [|lia]. apply CK3 in Z37; [|lia]. apply CK3 in Z38; [|lia]. clear CK3 Hevz1.
set (dl1 := put_dec_c.dec_len maj 1) in *.
(* two new atoms: 528 = en (mf+208) and 529 = &ev[en], with the alias ev + en = 529 *)
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msx |- _ =>
  pose proof (st_ok_pi_havoc_hi 528 Ex ssx msx [Z_to_bv 64 dl1; Z_to_bv 64 (SF + 288 + dl1)] HS
    ltac:(change (length _) with 2%nat; vm_compute; reflexivity)) as HSh;
  assert (HEIh : img_env VAL A_LIM (havoc Ex 528 [Z_to_bv 64 dl1; Z_to_bv 64 (SF + 288 + dl1)]))
    by (apply img_env_havoc_hi; [apply img_env_havoc_hi; [assumption | cbv; lia] | cbv; lia]) end.
clear HS. rename HSh into HS.
lazymatch goal with HS : st_ok_pi _ _ (havoc ?Ex 528 ?ws) _ _ |- _ =>
  assert (A528 : ew (havoc Ex 528 ws) 528 = Z_to_bv 64 dl1) by (exact (YN3v.ew_havoc_new Ex 528 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
  assert (A529 : ew (havoc Ex 528 ws) 529 = Z_to_bv 64 (SF + 288 + dl1))
    by (exact (YN3v.ew_havoc_new Ex 528 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
lazymatch goal with HS : st_ok_pi _ _ ?E2 _ _ |- _ =>
  assert (U9y : bv_unsigned (ew E2 9) = mf) by (d3_env; exact U9);
  assert (U20y : bv_unsigned (ew E2 20) = SF + 288) by (d3_env; exact U20);
  assert (U25y : bv_unsigned (ew E2 25) = pl) by (d3_env; exact U25) end.
assert (U528 : bv_unsigned (ew _ 528) = dl1) by (rewrite A528; apply unsigned_lit_small; lia).
assert (U529 : bv_unsigned (ew _ 529) = SF + 288 + dl1) by (rewrite A529; apply unsigned_lit_small; lia).
apply (st_ok_pi_add_fact _ _ _ 529 (mkAF 4096 (2 ^ 47 - 1024) 0)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U529; rewrite Z.pow_0_r, Z.mod_1_r; lia].
apply (d3_add_alias _ _ _ (SAlu ALU_ADD (SOff 20 0) (SOff 528 0)) (SOff 529 0)) in HS;
  [| apply U_inj; rewrite U_SAlu, !U_SOff, U20y, U528, U529; cbn [zalu_raw];
     rewrite !Z.add_0_r; rewrite (zcanon_id (SF + 288)) by (unfold M64; lia);
     rewrite (zcanon_id dl1) by (unfold M64; lia); reflexivity].
apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 529%nat) 0 1 0 1 [])) in HS;
[| reflexivity
 | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
   rewrite U529; split; [lia|]; split; [lia|]; split;
   [ intros o Ho; cbn [restrict ms_mem mkst]; apply (apresent_writable SEGS);
     apply (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SF + 288 + dl1 + o) HJ3 ltac:(
       right; right; right; exists 4, pos; split; [left; reflexivity|]; left;
       unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFa3, HFB; lia)))
   | apply Forall_nil ]
 | cbn [ss_mem all_disjoint]; repeat split; (eapply d3_ext; [exact U529 | first [exact U9y | exact U25y] |]); d3_xlia ].
apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 9%nat) 208 216 208 216 [YP09.mkChunk 208 (CVal 8 (SOff 528 0))])) in HS;
[| reflexivity
 | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
   rewrite U9y; split; [lia|]; split; [lia|]; split;
   [ intros o Ho; cbn [restrict ms_mem]; apply (apresent_writable SEGS);
     pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _); apply Hpres3; lia
   | constructor; [|constructor]; cbn [restrict ms_mem];
     apply (chunk_ok_val SEGS _ _ mf 208 8 (SOff 528 0) dl1);
     [ cbn [sv_denot]; rewrite A528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
     | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | rewrite Z.add_0_l in HV3; exact HV3 ] ]
 | cbn [ss_mem all_disjoint]; repeat split; (eapply d3_ext; [exact U9y | first [exact U529 | exact U9y | exact U25y] |]); d3_xlia ].
clear SHOK.
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => assert (SHOK : sh_ok SEGS d3_Bx [mkSHE 529 0 1] Ex (rd W3 mem3)) end.
{ unfold sh_ok. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W3) mem3 _ d3_Bx 529 (SF + 288 + dl1) 1 (SF + 288 + dl1) 0 1).
  - apply (d3_ev_addr _ SF); [clear - HSF64; lia | | lia | lia].
    intros j Hj. change (shadow_addr SF) with sh.
    assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia. destruct Hj3 as [-> | [-> | ->]];
    [rewrite Z.add_0_r; exact Z36 | replace (sh + 36 + 1) with (sh + 37) by lia; exact Z37
    | replace (sh + 36 + 2) with (sh + 38) by lia; exact Z38].
  - unfold d3_Bx. apply (U_atom _ 14 SHADOW_OFF); [d3_env; exact G14 | unfold SHADOW_OFF; lia].
  - apply (U_atom _ 529 (SF + 288 + dl1) A529). lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. d3_xlia. }
(* ---- run 6: ev[en++] = '.' (0x8100c .. put_dec #2 at 0x81044) ---- *)
paj_run_tok RUN HS HJ3 SHOK d3_Bspan.
{ d3_rs.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0)); [reflexivity | rewrite U9y; unfold sp0; ring | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (SF + 288 + dl1)); [reflexivity | exact U529 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
    left. unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFa3, HFB; lia. }
  d3_ro. d3_ro. apply awr_ok_nil. }
pose proof (d3_kc_refl SF W3 mem3) as HKC.
d3_kcr mf HSHA ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H; try rewrite U529 in H).
pose proof (d3_kr_refl (SF + 288) (SF + 288 + dl1) W3 mem3) as KEV1.
d3_krr ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H; try rewrite U529 in H).
d3_kkr ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H; try rewrite U529 in H).
(* what run 6 stored: en = dl1 + 1 at mf+208 and '.' at ev[dl1] *)
lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HMO; cbn [ss_mem setpc ms_mem restrict] in HMO;
  pose proof (d3_chunk_val Ex _ _ 9 208 216 208 216 _ 208 8 (SOff 528 1) (dl1 + 1) HMO ltac:(d3_in) ltac:(d3_in)
    ltac:(cbn [sv_denot]; d3_env; rewrite U528; reflexivity) ltac:(lia)) as V208b;
  pose proof (d3_chunk_val Ex _ _ 529 0 1 0 1 _ 0 1 (SLit 46) 46 HMO ltac:(d3_in) ltac:(d3_in) eq_refl ltac:(lia)) as VDOT;
  assert (U9z : bv_unsigned (ew Ex 9) = mf) by (d3_env; exact U9);
  assert (U529z : bv_unsigned (ew Ex 529) = SF + 288 + dl1) by (d3_env; exact U529);
  rewrite U9z in V208b; rewrite U529z, Z.add_0_r in VDOT; apply d3_garr8_1 in VDOT; [|lia]; clear HMO end.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  pose proof (d3_kr_refl (SF + 288 + dl1) (SF + 288 + dl1 + 1) W3 (ms_mem msx)) as KDOT end.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  prreg HS (10%bv : bv 5) Rb0; prreg HS (11%bv : bv 5) Rb1; prreg HS (12%bv : bv 5) Rb2; prreg HS (13%bv : bv 5) Rb3;
  prreg HS (1%bv : bv 5) Rbra; prreg HS (2%bv : bv 5) Rbsp; prreg HS (3%bv : bv 5) Rbgp; prreg HS (4%bv : bv 5) Rbtp end.
rewrite G20 in Rb0. rewrite U9 in Rb1. rewrite G26 in Rb2. rewrite G2 in Rbsp. rewrite G3 in Rbgp. rewrite G4 in Rbtp.
pose proof (d3_dl1 mnr Rmi) as Hdl2.
assert (Hnev3 : st_nev S3 <= EV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hn3 & _). clear - Hn3 Hnev0 Hk HEV. unfold EV_LLVMF in *. lia. }
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  assert (Usp2 : spZ (ms_regs msx) = mf) by (unfold spZ; rewrite Rbsp; apply unsigned_lit_small; lia);
  assert (Hevz2 : forall j, 0 <= j < 3 -> aview SEGS (w_H W3) (ms_mem msx) (shadow_addr SF + 36 + j) = Some 0)
    by (intros j Hj; replace (shadow_addr SF + 36 + j) with (shadow_addr SF + (36 + j)) by lia;
        rewrite (HKC (36 + j) ltac:(lia)); change (shadow_addr SF) with sh;
        assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia; destruct Hj3 as [-> | [-> | ->]];
        [exact Z36 | exact Z37 | exact Z38]) end.
d3_clearU E0.
pmkst HS.
(* ---- put_dec(ev, &en, minor, 1), 0x81044 ---- *)
eapply SRr_bind.
{ apply (d3_putdec g pos mf W3 _ _ _ ly3 S3 (4 * Z.of_nat i + 3) (dl1 + 1) mnr 1 2364 HJ3 Hfr3 Hnev3 Hmfb Hmf32 Hmf0 HSF0
    ltac:(lia) HSFapp HSF64 Rb0 Rb1 Rb2 Rb3 Rbra
    ltac:(lia) eq_refl Rbsp Rbgp Rbtp Rmi ltac:(lia) ltac:(lia) ltac:(lia) V208b Hevz2). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfr4 & Hbl4 & HK4 & HG4 & HV4).
rewrite Usp2 in HK4. unfold EV_PUT_DEC in HJ4. rewrite Z.add_0_r in HJ4. rewrite Hfr3 in Hfr4.
assert (EFa4 : frame_addr ly4 4 pos = SF).
{ pose proof HJ4 as (_ & Hly4 & _). destruct Hly4 as (_ & _ & _ & _ & _ & EF4 & _).
  unfold SF, SFa, frame_addr. rewrite EF4. reflexivity. }
assert (Hperm3 : Permutation (ablocks B ly3 S3) (ablocks B ly2 S2)) by (rewrite Hbl3; apply Permutation_refl).
pose proof (d3_kk_tcj ly2 S2 mf SF W2 mem2 _ ly3 S3 W3 _ W4 mem4 _ pos HKK HK4 Hfr3 EFa3 ltac:(lia)
  Hperm3 ltac:(intros a Ha; cbn beta in Ha; unfold d3_wr; d3_slim; lia)) as HKK4.
clear HKK. rename HKK4 into HKK.
pose proof (d3_kc_tcj SF mf W3 mem3 _ ly3 S3 W3 _ W4 mem4 _ pos HKC HK4 Hfr3 EFa3 ltac:(lia) HSHA
  ltac:(intros a Ha; cbn beta in Ha; d3_slim; lia)) as HKC4.
clear HKC. rename HKC4 into HKC.
pose proof (d3_kr_tcj _ _ _ _ _ ly3 S3 W3 _ W4 mem4 _ pos mf SF KEV1 HK4 Hfr3 EFa3 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(intros a Ha; cbn beta; d3_slim; lia)) as KEV1'. clear KEV1. rename KEV1' into KEV1.
pose proof (d3_kr_tcj _ _ _ _ _ ly3 S3 W3 _ W4 mem4 _ pos mf SF KDOT HK4 Hfr3 EFa3 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(intros a Ha; cbn beta; d3_slim; lia)) as KDOT'. clear KDOT. rename KDOT' into KDOT.
set (dl2 := put_dec_c.dec_len mnr 1) in *.
pose proof (d3_kr_refl (SF + 288 + (dl1 + 1)) (SF + 288 + (dl1 + 1) + dl2) W4 mem4) as KEV2.
pose proof (d3_kr_refl (mf + 208) (mf + 216) W4 mem4) as KEN.
lazymatch goal with HS : st_ok _ ?Ex ?ssx _ |- _ =>
  assert (U25z : bv_unsigned (ew Ex 25) = pl) by (d3_env; exact U25);
  let K := eval vm_compute in (run_K A_LIM d3_Bx [] ssx) in
  jafter_call_keep_hi HS K regs4 (mrestrict (w_H W4) mem4) HP4 [2;3]%nat HS4 end.
match type of HS4 with ?Q -> _ => assert (HQ : Q); [|specialize (HS4 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
  - eapply d3_rk_ro; [d3_env; exact U9 |]. intros a Ha.
    apply (d3_tcj_keep _ _ _ _ _ _ _ mf _ pos SF a HK4 Hfr3 EFa3 ltac:(lia) ltac:(lia)); [left; lia | cbn beta; lia].
  - eapply d3_rk_ro; [d3_env; exact U25 |]. intros a Ha.
    apply (d3_tcj_keep _ _ _ _ _ _ _ mf _ pos SF a HK4 Hfr3 EFa3 ltac:(lia) ltac:(lia));
      [right; right; right; exists pl, k; split; [rewrite Hbl3; exact Hinpl | lia] | cbn beta; d3_xlia]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS. rewrite Rbra.
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (HEIc2 : img_env VAL A_LIM Ex) by (apply img_env_havoc_hi; [assumption | cbv; lia]) end.
(* ---- run 7: put_dec #3's arguments (0x81048 .. 0x81058); no memory access ---- *)
paj_run_shc RUNP RUNC HS HJ4.
{ d3_rs. d3_ro. d3_ro. apply awr_ok_nil. }
d3_kcr mf HSHA ltac:(fun H => idtac).
d3_krr ltac:(fun H => idtac).
d3_kkr ltac:(fun H => idtac).
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  prreg HS (10%bv : bv 5) Rc0; prreg HS (11%bv : bv 5) Rc1; prreg HS (12%bv : bv 5) Rc2; prreg HS (13%bv : bv 5) Rc3;
  prreg HS (1%bv : bv 5) Rcra; prreg HS (2%bv : bv 5) Rcsp; prreg HS (3%bv : bv 5) Rcgp; prreg HS (4%bv : bv 5) Rctp end.
rewrite G20 in Rc0. rewrite U9 in Rc1. rewrite G24 in Rc2. rewrite G2 in Rcsp. rewrite G3 in Rcgp. rewrite G4 in Rctp.
pose proof (d3_dl2 pat Rpa) as Hdl3.
assert (Hnev4 : st_nev S4 <= EV_MAX).
{ pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hn4 & _). clear - Hn4 Hnev0 Hk HEV. unfold EV_LLVMF in *. lia. }
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  assert (Usp3 : spZ (ms_regs msx) = mf) by (unfold spZ; rewrite Rcsp; apply unsigned_lit_small; lia);
  assert (V208c : val_mem SEGS (rd W4 (ms_mem msx)) (mf + 208) 8 (dl1 + 1 + dl2))
    by (apply (val_mem_moved SEGS (w_H W4) (w_H W4) mem4 (ms_mem msx) (mf + 208) (mf + 208) 8 _);
        [intros kk Hkk; apply KEN; lia | exact HV4]);
  assert (Hevz3 : forall j, 0 <= j < 3 -> aview SEGS (w_H W4) (ms_mem msx) (shadow_addr SF + 36 + j) = Some 0)
    by (intros j Hj; replace (shadow_addr SF + 36 + j) with (shadow_addr SF + (36 + j)) by lia;
        rewrite (HKC (36 + j) ltac:(lia)); change (shadow_addr SF) with sh;
        assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia; destruct Hj3 as [-> | [-> | ->]];
        [exact Z36 | exact Z37 | exact Z38]) end.
d3_clearU E0.
pmkst HS.
(* ---- put_dec(ev, &en, patch, 2), 0x81058 ---- *)
eapply SRr_bind.
{ apply (d3_putdec g pos mf W4 _ _ _ ly4 S4 (4 * Z.of_nat i + 3) (dl1 + 1 + dl2) pat 2 2384 HJ4 Hfr4 Hnev4 Hmfb Hmf32 Hmf0
    HSF0 ltac:(lia) HSFapp HSF64 Rc0 Rc1 Rc2 Rc3 Rcra
    ltac:(lia) eq_refl Rcsp Rcgp Rctp Rpa ltac:(lia) ltac:(lia) ltac:(lia) V208c Hevz3). }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hfr5 & Hbl5 & HK5 & HG5 & HV5).
rewrite Usp3 in HK5. unfold EV_PUT_DEC in HJ5. rewrite Z.add_0_r in HJ5. rewrite Hfr4 in Hfr5.
assert (EFa5 : frame_addr ly5 4 pos = SF).
{ pose proof HJ5 as (_ & Hly5 & _). destruct Hly5 as (_ & _ & _ & _ & _ & EF5 & _).
  unfold SF, SFa, frame_addr. rewrite EF5. reflexivity. }
assert (Hperm4 : Permutation (ablocks B ly4 S4) (ablocks B ly2 S2)) by (rewrite Hbl4, Hbl3; apply Permutation_refl).
pose proof (d3_kk_tcj ly2 S2 mf SF W2 mem2 _ ly4 S4 W4 _ W5 mem5 _ pos HKK HK5 Hfr4 EFa4 ltac:(lia)
  Hperm4 ltac:(intros a Ha; cbn beta in Ha; unfold d3_wr; d3_slim; lia)) as HKK5.
clear HKK. rename HKK5 into HKK.
pose proof (d3_kc_tcj SF mf W3 mem3 _ ly4 S4 W4 _ W5 mem5 _ pos HKC HK5 Hfr4 EFa4 ltac:(lia) HSHA
  ltac:(intros a Ha; cbn beta in Ha; d3_slim; lia)) as HKC5.
clear HKC. rename HKC5 into HKC.
pose proof (d3_kr_tcj _ _ _ _ _ ly4 S4 W4 _ W5 mem5 _ pos mf SF KEV1 HK5 Hfr4 EFa4 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(intros a Ha; cbn beta; d3_slim; lia)) as KEV1'. clear KEV1. rename KEV1' into KEV1.
pose proof (d3_kr_tcj _ _ _ _ _ ly4 S4 W4 _ W5 mem5 _ pos mf SF KDOT HK5 Hfr4 EFa4 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(intros a Ha; cbn beta; d3_slim; lia)) as KDOT'. clear KDOT. rename KDOT' into KDOT.
pose proof (d3_kr_tcj _ _ _ _ _ ly4 S4 W4 _ W5 mem5 _ pos mf SF KEV2 HK5 Hfr4 EFa4 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(intros a Ha; cbn beta; d3_slim; lia)) as KEV2'. clear KEV2. rename KEV2' into KEV2.
clear KEN.
set (dl3 := put_dec_c.dec_len pat 2) in *.
set (en := dl1 + 1 + dl2 + dl3) in *.
(* ev[0 .. en) is complete: one byte array from here on *)
assert (GE0 : garr8 SEGS (rd W5 mem5) (SF + 288)
  (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC maj 1) ++ [46] ++
   map (fun b : byte => bv_unsigned b) (IdentSpec.DEC mnr 1) ++ map (fun b : byte => bv_unsigned b) (IdentSpec.DEC pat 2))).
{ apply (d3_garr8_app' _ _ _ (SF + 288 + dl1)).
  { apply (d3_garr8_kr' (SF + 288) dl1 W3 mem3 W5 _ _ KEV1); [rewrite length_map; reflexivity | rewrite Z.add_0_r in HG3; exact HG3]. }
  { rewrite length_map. reflexivity. }
  apply (d3_garr8_app' _ _ _ (SF + 288 + (dl1 + 1))).
  { apply (d3_garr8_kr' (SF + 288 + dl1) 1 W3 _ W5 _ _ KDOT); [reflexivity | exact VDOT]. }
  { cbn [length]. lia. }
  apply (d3_garr8_app' _ _ _ (SF + 288 + (dl1 + 1 + dl2))).
  { apply (d3_garr8_kr' (SF + 288 + (dl1 + 1)) dl2 W4 mem4 W5 _ _ KEV2); [rewrite length_map; reflexivity | exact HG4]. }
  { rewrite length_map. unfold dl2, put_dec_c.dec_len. lia. }
  exact HG5. }
clear KEV1 KDOT KEV2 HG3 HG4 HG5 VDOT.
pose proof (d3_kr_refl (SF + 288) (SF + 288 + en) W5 mem5) as KEVA.
lazymatch goal with HS : st_ok _ ?Ex ?ssx _ |- _ =>
  assert (U9w : bv_unsigned (ew Ex 9) = mf) by (d3_env; exact U9);
  assert (U25w : bv_unsigned (ew Ex 25) = pl) by (d3_env; exact U25);
  let K := eval vm_compute in (run_K A_LIM d3_Bx [] ssx) in
  jafter_call_keep_hi HS K regs5 (mrestrict (w_H W5) mem5) HP5 [0;1]%nat HS5 end.
match type of HS5 with ?Q -> _ => assert (HQ : Q); [|specialize (HS5 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
  - eapply d3_rk_ro; [d3_env; exact U9 |]. intros a Ha.
    apply (d3_tcj_keep _ _ _ _ _ _ _ mf _ pos SF a HK5 Hfr4 EFa4 ltac:(lia) ltac:(lia)); [left; lia | cbn beta; lia].
  - eapply d3_rk_ro; [d3_env; exact U25 |]. intros a Ha.
    apply (d3_tcj_keep _ _ _ _ _ _ _ mf _ pos SF a HK5 Hfr4 EFa4 ltac:(lia) ltac:(lia));
      [right; right; right; exists pl, k; split; [rewrite Hbl4, Hbl3; exact Hinpl | lia] | cbn beta; d3_xlia]. }
clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS. rewrite Rcra.
(* ---- back at 0x8105c: two new atoms, 800 = en (mf+208) and 801 = &ev[en] ---- *)
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msx |- _ =>
  pose proof (st_ok_pi_havoc_hi 800 Ex ssx msx [Z_to_bv 64 en; Z_to_bv 64 (SF + 288 + en)] HS
    ltac:(change (length _) with 2%nat; vm_compute; reflexivity)) as HSh;
  assert (HEIh5 : img_env VAL A_LIM (havoc Ex 800 [Z_to_bv 64 en; Z_to_bv 64 (SF + 288 + en)]))
    by (repeat first [assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia]]) end.
clear HS. rename HSh into HS.
lazymatch goal with HS : st_ok_pi _ _ (havoc ?Ex 800 ?ws) _ _ |- _ =>
  assert (A800 : ew (havoc Ex 800 ws) 800 = Z_to_bv 64 en) by (exact (YN3v.ew_havoc_new Ex 800 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
  assert (A801 : ew (havoc Ex 800 ws) 801 = Z_to_bv 64 (SF + 288 + en))
    by (exact (YN3v.ew_havoc_new Ex 800 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
assert (Hen : en = rvs_LV maj mnr pat) by (unfold en, dl1, dl2, dl3; exact (d3_LV maj mnr pat Rma Rmi Rpa)).
assert (Hen16 : 4 <= en <= 16) by (unfold en; lia).
lazymatch goal with HS : st_ok_pi _ _ ?E2 _ _ |- _ =>
  assert (U9v : bv_unsigned (ew E2 9) = mf) by (d3_env; exact U9);
  assert (U20v : bv_unsigned (ew E2 20) = SF + 288) by (d3_env; exact U20);
  assert (U25v : bv_unsigned (ew E2 25) = pl) by (d3_env; exact U25) end.
assert (U800 : bv_unsigned (ew _ 800) = en) by (rewrite A800; apply unsigned_lit_small; lia).
assert (U801 : bv_unsigned (ew _ 801) = SF + 288 + en) by (rewrite A801; apply unsigned_lit_small; lia).
apply (st_ok_pi_add_fact _ _ _ 801 (mkAF 4096 (2 ^ 47 - 1024) 0)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U801; rewrite Z.pow_0_r, Z.mod_1_r; lia].
apply (d3_add_alias _ _ _ (SAlu ALU_ADD (SOff 20 0) (SOff 800 0)) (SOff 801 0)) in HS;
  [| apply U_inj; rewrite U_SAlu, !U_SOff, U20v, U800, U801; cbn [zalu_raw];
     rewrite !Z.add_0_r; rewrite (zcanon_id (SF + 288)) by (unfold M64; lia);
     rewrite (zcanon_id en) by (unfold M64; lia); reflexivity].
apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 801%nat) 0 1 0 1 [])) in HS;
[| reflexivity
 | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
   rewrite U801; split; [lia|]; split; [lia|]; split;
   [ intros o Ho; cbn [restrict ms_mem mkst]; apply (apresent_writable SEGS);
     apply (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SF + 288 + en + o) HJ5 ltac:(
       right; right; right; exists 4, pos; split; [left; reflexivity|]; left;
       unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFa5, HFB; lia)))
   | apply Forall_nil ]
 | cbn [ss_mem all_disjoint]; repeat split; (eapply d3_ext; [exact U801 | first [exact U9v | exact U25v] |]); d3_xlia ].
apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 9%nat) 208 216 208 216 [YP09.mkChunk 208 (CVal 8 (SOff 800 0))])) in HS;
[| reflexivity
 | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
   rewrite U9v; split; [lia|]; split; [lia|]; split;
   [ intros o Ho; cbn [restrict ms_mem]; apply (apresent_writable SEGS);
     pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _); apply Hpres5; lia
   | constructor; [|constructor]; cbn [restrict ms_mem];
     apply (chunk_ok_val SEGS _ _ mf 208 8 (SOff 800 0) en);
     [ cbn [sv_denot]; rewrite A800, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
     | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | first [exact HV5 | unfold en; exact HV5] ] ]
 | cbn [ss_mem all_disjoint]; repeat split; (eapply d3_ext; [exact U9v | first [exact U801 | exact U9v | exact U25v] |]); d3_xlia ].
clear SHOK.
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => assert (SHOK : sh_ok SEGS d3_Bx [mkSHE 801 0 1] Ex (rd W5 mem5)) end.
{ unfold sh_ok. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W5) mem5 _ d3_Bx 801 (SF + 288 + en) 1 (SF + 288 + en) 0 1).
  - apply (d3_ev_addr _ SF); [clear - HSF64; lia | | lia | lia].
    intros j Hj. replace (shadow_addr SF + 36 + j) with (shadow_addr SF + (36 + j)) by lia.
    rewrite (HKC (36 + j) ltac:(lia)). change (shadow_addr SF) with sh.
    assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia. destruct Hj3 as [-> | [-> | ->]]; [exact Z36 | exact Z37 | exact Z38].
  - unfold d3_Bx. apply (U_atom _ 14 SHADOW_OFF); [d3_env; exact G14 | unfold SHADOW_OFF; lia].
  - apply (U_atom _ 801 (SF + 288 + en) A801). lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. d3_xlia. }
(* ---- run 8: ev[en] = 0 and the arguments of reac_identity_reac_ver_str (0x8105c .. 0x81094) ---- *)
paj_run_tok RUN HS HJ5 SHOK d3_Bspan.
{ d3_rs.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0)); [reflexivity | rewrite U9v; unfold sp0; ring | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 801%nat (SF + 288 + en)); [reflexivity | exact U801 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
    left. unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFa5, HFB; lia. }
  d3_ro. d3_ro. apply awr_ok_nil. }
d3_kcr mf HSHA ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H; try rewrite U801 in H).
d3_krr ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H; try rewrite U801 in H).
d3_kkr ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H; try rewrite U801 in H).
lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HMO; cbn [ss_mem setpc ms_mem restrict] in HMO;
  pose proof (d3_chunk_val Ex _ _ 801 0 1 0 1 _ 0 1 (SLit 0) 0 HMO ltac:(d3_in) ltac:(d3_in) eq_refl ltac:(lia)) as VZ;
  assert (U801z : bv_unsigned (ew Ex 801) = SF + 288 + en) by (d3_env; exact U801);
  rewrite U801z, Z.add_0_r in VZ; apply d3_garr8_1 in VZ; [|lia]; clear HMO;
  pose proof (d3_kr_refl (SF + 288 + en) (SF + 288 + en + 1) W5 (ms_mem msx)) as KZ end.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  prreg HS (10%bv : bv 5) Rd0; prreg HS (11%bv : bv 5) Rd1; prreg HS (12%bv : bv 5) Rd2; prreg HS (13%bv : bv 5) Rd3;
  prreg HS (14%bv : bv 5) Rd4;
  prreg HS (1%bv : bv 5) Rdra; prreg HS (2%bv : bv 5) Rdsp; prreg HS (3%bv : bv 5) Rdgp; prreg HS (4%bv : bv 5) Rdtp end.
rewrite G18 in Rd0. rewrite G26 in Rd1. rewrite G24 in Rd2. rewrite U20 in Rd3.
replace (SF + 288 + -64) with (SF + 224) in Rd3 by lia.
rewrite G2 in Rdsp. rewrite G3 in Rdgp. rewrite G4 in Rdtp.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  assert (Usp4 : spZ (ms_regs msx) = mf) by (unfold spZ; rewrite Rdsp; apply unsigned_lit_small; lia);
  assert (Zv : forall c v, 28 <= c <= 30 -> aview SEGS (w_H W3) mem3 (sh + c) = Some v ->
    aview SEGS (w_H W5) (ms_mem msx) (shadow_addr SF + c) = Some v)
    by (intros c v Hcc Hv; rewrite (HKC c ltac:(lia)); exact Hv) end.
d3_clearU E0.
pmkst HS.
(* ---- reac_identity_reac_ver_str(major, minor, patch, v, 20), 0x81094 ---- *)
eapply SRr_bind.
{ apply (d3_verstr g pos mf W5 _ _ _ ly5 S5 (4 * Z.of_nat i + 3) maj mnr pat 2444 HJ5 Hfr5 Hmfb Hmf32 Hmf0 HSF0
    ltac:(lia) HSF64 Rd0 Rd1 Rd2 Rd3 Rd4 Rdra ltac:(lia) eq_refl Rdsp Rdgp Rdtp Rma Rmi Rpa
    (Zv 28 0 ltac:(lia) Z28) (Zv 29 0 ltac:(lia) Z29) (Zv 30 4 ltac:(lia) Z30)). }
cbv beta. intros W6 c6 Hwle6 (-> & ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hbl6 & Hfr6 & HIF6).
assert (Hnf : rvs_fails (SF + 224) 20 = false)
  by (unfold rvs_fails; apply orb_false_iff; split; [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia]).
change (SFa g pos) with SF in HIF6. rewrite Hnf in HIF6. destruct HIF6 as (HR6 & HG6 & HK6). clear Hnf.
unfold EV_REAC_VER_STR in HJ6. rewrite Z.add_0_r in HJ6. rewrite Hfr5 in Hfr6. rewrite Usp4 in HK6. rewrite <- Hen in HR6, HK6.
assert (EFa6 : frame_addr ly6 4 pos = SF).
{ pose proof HJ6 as (_ & Hly6 & _). destruct Hly6 as (_ & _ & _ & _ & _ & EF6 & _).
  unfold SF, SFa, frame_addr. rewrite EF6. reflexivity. }
assert (Hperm5 : Permutation (ablocks B ly5 S5) (ablocks B ly2 S2)) by (rewrite Hbl5, Hbl4, Hbl3; apply Permutation_refl).
pose proof (d3_kk_tcj ly2 S2 mf SF W2 mem2 _ ly5 S5 W5 _ W5 mem6 _ pos HKK HK6 Hfr5 EFa5 ltac:(lia)
  Hperm5 ltac:(intros a Ha; cbn beta in Ha; unfold d3_wr; d3_slim; lia)) as HKK6.
clear HKK. rename HKK6 into HKK.
pose proof (d3_kc_tcj SF mf W3 mem3 _ ly5 S5 W5 _ W5 mem6 _ pos HKC HK6 Hfr5 EFa5 ltac:(lia) HSHA
  ltac:(intros a Ha; cbn beta in Ha; d3_slim; lia)) as HKC6.
clear HKC. rename HKC6 into HKC.
pose proof (d3_kr_tcj _ _ _ _ _ ly5 S5 W5 _ W5 mem6 _ pos mf SF KEVA HK6 Hfr5 EFa5 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(intros a Ha; cbn beta; d3_slim; lia)) as KEVA'. clear KEVA. rename KEVA' into KEVA.
pose proof (d3_kr_tcj _ _ _ _ _ ly5 S5 W5 _ W5 mem6 _ pos mf SF KZ HK6 Hfr5 EFa5 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(intros a Ha; cbn beta; d3_slim; lia)) as KZ'. clear KZ. rename KZ' into KZ.
pose proof (d3_kr_refl (SF + 224) (SF + 224 + en + 1) W5 mem6) as KV.
lazymatch goal with HS : st_ok _ ?Ex ?ssx _ |- _ =>
  assert (U9u : bv_unsigned (ew Ex 9) = mf) by (d3_env; exact U9);
  assert (U25u : bv_unsigned (ew Ex 25) = pl) by (d3_env; exact U25);
  let K := eval vm_compute in (run_K A_LIM d3_Bx [] ssx) in
  jafter_call_keep_hi HS K regs6 (mrestrict (w_H W5) mem6) HP6 [2;3]%nat HS6 end.
match type of HS6 with ?Q -> _ => assert (HQ : Q); [|specialize (HS6 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
  - eapply d3_rk_ro; [d3_env; exact U9 |]. intros a Ha.
    apply (d3_tcj_keep _ _ _ _ _ _ _ mf _ pos SF a HK6 Hfr5 EFa5 ltac:(lia) ltac:(lia)); [left; lia | cbn beta; lia].
  - eapply d3_rk_ro; [d3_env; exact U25 |]. intros a Ha.
    apply (d3_tcj_keep _ _ _ _ _ _ _ mf _ pos SF a HK6 Hfr5 EFa5 ltac:(lia) ltac:(lia));
      [right; right; right; exists pl, k; split; [rewrite Hbl5, Hbl4, Hbl3; exact Hinpl | lia] | cbn beta; d3_xlia]. }
clear HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS. rewrite Rdra.
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (HEIh6 : img_env VAL A_LIM Ex)
    by (repeat first [assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia]]) end.
clear SHOK.
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (SHOK : sh_ok SEGS d3_Bx [] Ex (rd W5 mem6)) by apply Forall_nil end.
(* ---- run 9: w >= 0, w = en, and bcmp's arguments (0x81098 .. 0x810b8) ---- *)
paj_run_tok RUN HS HJ6 SHOK d3_Bspan.
{ d3_rs. d3_ro. d3_ro. apply awr_ok_nil. }
psrr_branch_tok RUN BR HS SHOK d3_Bspan.
2: { exfalso. d3_norm Hc. rewrite HR6 in Hc. try unfold w64 in Hc. rewrite YO0c.branch_ge in Hc.
     rewrite !unsigned_lit_small in Hc by lia. rewrite !YO0b.s64_small in Hc by lia.
     apply negb_false_iff, Z.ltb_lt in Hc. lia. }
clear Hc.
paj_run_tok RUN HS HJ6 SHOK d3_Bspan.
{ d3_rs. d3_ro. d3_ro. apply awr_ok_nil. }
psrr_branch_tok RUN BR HS SHOK d3_Bspan.
2: { exfalso. d3_norm Hc. rewrite HR6 in Hc. try unfold w64 in Hc. rewrite YO0c.branch_eq in Hc.
     rewrite !unsigned_lit_small in Hc by lia. rewrite Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ6 SHOK d3_Bspan.
{ d3_rs. d3_ro. d3_ro. apply awr_ok_nil. }
d3_kcr mf HSHA ltac:(fun H => idtac). d3_krr ltac:(fun H => idtac). d3_kkr ltac:(fun H => idtac).
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  prreg HS (10%bv : bv 5) Re0; prreg HS (11%bv : bv 5) Re1; prreg HS (12%bv : bv 5) Re2;
  prreg HS (1%bv : bv 5) Rera; prreg HS (2%bv : bv 5) Resp; prreg HS (3%bv : bv 5) Regp; prreg HS (4%bv : bv 5) Retp end.
d3_norm Re2. rewrite unsigned_lit_small in Re2 by lia.
rewrite U20 in Re0. replace (SF + 288 + -64) with (SF + 224) in Re0 by lia. rewrite G20 in Re1.
rewrite G2 in Resp. rewrite G3 in Regp. rewrite G4 in Retp.
pose proof (d3_dl1 maj Rma) as Hdl1'. pose proof (d3_dl1 mnr Rmi) as Hdl2'. pose proof (d3_dl2 pat Rpa) as Hdl3'.
assert (HLEN : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC maj 1) ++ [46] ++
    map (fun b : byte => bv_unsigned b) (IdentSpec.DEC mnr 1) ++ map (fun b : byte => bv_unsigned b) (IdentSpec.DEC pat 2) ++ [0]))
    = en + 1).
{ rewrite !length_app, !length_map. cbn [length]. unfold en, dl1, dl2, dl3, put_dec_c.dec_len. lia. }
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  assert (GV : garr8 SEGS (rd W5 (ms_mem msx)) (SF + 224)
    (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC maj 1) ++ [46] ++
     map (fun b : byte => bv_unsigned b) (IdentSpec.DEC mnr 1) ++ map (fun b : byte => bv_unsigned b) (IdentSpec.DEC pat 2) ++ [0]));
  [ rewrite <- (d3_bytes_eq maj mnr pat Rma Rmi Rpa);
    apply (d3_garr8_kr' (SF + 224) (en + 1) W5 mem6 W5 (ms_mem msx) _);
    [ replace (SF + 224 + (en + 1)) with (SF + 224 + en + 1) by lia; exact KV
    | rewrite (d3_bytes_eq maj mnr pat Rma Rmi Rpa); exact HLEN | exact HG6 ] |];
  assert (GE : garr8 SEGS (rd W5 (ms_mem msx)) (SF + 288)
    (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC maj 1) ++ [46] ++
     map (fun b : byte => bv_unsigned b) (IdentSpec.DEC mnr 1) ++ map (fun b : byte => bv_unsigned b) (IdentSpec.DEC pat 2) ++ [0])) end.
{ set (LA := map (fun b : byte => bv_unsigned b) (IdentSpec.DEC maj 1)).
  set (LB := map (fun b : byte => bv_unsigned b) (IdentSpec.DEC mnr 1)).
  set (LC := map (fun b : byte => bv_unsigned b) (IdentSpec.DEC pat 2)).
  replace (LA ++ [46] ++ LB ++ LC ++ [0]) with ((LA ++ [46] ++ LB ++ LC) ++ [0]) by (rewrite <- !app_assoc; reflexivity).
  apply (d3_garr8_app' _ _ _ (SF + 288 + en)).
  - apply (d3_garr8_kr' (SF + 288) en W5 mem5 W5 _ _ KEVA); [| exact GE0].
    unfold LA, LB, LC. rewrite !length_app, !length_map. cbn [length]. unfold en, dl1, dl2, dl3, put_dec_c.dec_len. lia.
  - unfold LA, LB, LC. rewrite !length_app, !length_map. cbn [length]. unfold en, dl1, dl2, dl3, put_dec_c.dec_len. lia.
  - apply (d3_garr8_kr' (SF + 288 + en) 1 W5 _ W5 _ _ KZ); [reflexivity | exact VZ]. }
clear KEVA GE0 KZ KV HG6 VZ.
d3_clearU E0.
pmkst HS.
(* ---- bcmp(v, ev, en + 1), 0x810b8 ---- *)
eapply SRr_bind.
{ apply (d3_bcmp g pos mf W5 _ _ _ ly6 S6 (4 * Z.of_nat i + 3) (en + 1) 2480 HJ6 Hfr6 Hmfb Hmf32 Hmf0 HSF0 ltac:(lia)
    HSFapp HSF64 Re0 Re1 Re2 Rera ltac:(lia) eq_refl
    Resp Regp Retp ltac:(lia)).
  - exact (eq_trans (HKC 28 ltac:(lia)) Z28).
  - exact (eq_trans (HKC 29 ltac:(lia)) Z29).
  - exact (eq_trans (HKC 30 ltac:(lia)) Z30).
  - intros j Hj. change (SFa g pos) with SF. replace (shadow_addr SF + 36 + j) with (shadow_addr SF + (36 + j)) by lia.
    rewrite (HKC (36 + j) ltac:(lia)). change (shadow_addr SF) with sh.
    assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia. destruct Hj3 as [-> | [-> | ->]]; [exact Z36 | exact Z37 | exact Z38]. }
cbv beta. intros W7 c7 Hwle7 (-> & regs7 & mem7 & md7 & v7 & -> & HJ7 & HP7 & Hv7 & Hc7 & Hk7 & Hp7).
assert (Hv0 : v7 = w64 0).
{ apply Hc7. intros j Hj. apply (d3_bcmp_eq _ _ _ _ _ GV GE). rewrite HLEN. lia. }
clear Hc7 GV GE.
assert (HBL : forall b sz, In (b, sz) (ablocks B ly2 S2) -> b + req_size sz <= mf - 2 * ESTACK).
{ intros b sz Hin. destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b sz HAR2 Hin) as (_ & _ & Hce & _).
  unfold ESTACK. clear - Hce Hmf0. lia. }
pose proof (d3_kk_below ly2 S2 mf SF W2 mem2 W5 _ W5 mem7 (mf - 2 * ESTACK) HKK Hk7
  ltac:(unfold ESTACK; lia) ltac:(change (shadow_addr SF) with sh; unfold ESTACK; lia) HBL) as HKK7.
clear HKK. rename HKK7 into HKK.
pose proof (d3_kc_below SF W3 mem3 W5 _ W5 mem7 (mf - 2 * ESTACK) mf HKC Hk7
  ltac:(change (shadow_addr SF) with sh; lia) ltac:(change (shadow_addr SF) with sh; unfold ESTACK; lia)
  ltac:(unfold ESTACK; lia)) as HKC7.
clear HKC. rename HKC7 into HKC.
lazymatch goal with HS : st_ok _ ?Ex ?ssx _ |- _ =>
  assert (U9t : bv_unsigned (ew Ex 9) = mf) by (d3_env; exact U9);
  assert (U25t : bv_unsigned (ew Ex 25) = pl) by (d3_env; exact U25);
  let K := eval vm_compute in (run_K A_LIM d3_Bx [] ssx) in
  jafter_call_keep_hi HS K regs7 (mrestrict (w_H W5) mem7) HP7 [0;1]%nat HS7 end.
match type of HS7 with ?Q -> _ => assert (HQ : Q); [|specialize (HS7 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
  - eapply d3_rk_ro; [d3_env; exact U9 |]. intros a Ha. apply Hk7; [lia | unfold ESTACK; lia].
  - eapply d3_rk_ro; [d3_env; exact U25 |]. intros a Ha. apply Hk7; [lia | unfold ESTACK; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS7. rename HS7 into HS. try rewrite Rera.
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (HEIh7 : img_env VAL A_LIM Ex)
    by (repeat first [assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia]]) end.
assert (Hperm6 : Permutation (ablocks B ly6 S6) (ablocks B ly2 S2)) by (eapply Permutation_trans; [exact Hbl6 | exact Hperm5]).
assert (Hinpl6 : In (pl, k) (ablocks B ly6 S6)) by (apply (Permutation_in _ (Permutation_sym Hperm6)); exact Hinpl).
pose proof HJ7 as (HAR7 & _).
(* the hw region: SF+432 .. SF+444 (base atom 20, offsets 144 .. 156), written by the last token run *)
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (U20t : bv_unsigned (ew Ex 20) = SF + 288) by (d3_env; exact U20);
  assert (U9s : bv_unsigned (ew Ex 9) = mf) by (d3_env; exact U9);
  assert (U25s : bv_unsigned (ew Ex 25) = pl) by (d3_env; exact U25) end.
apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 20%nat) 144 156 144 156 [])) in HS;
[| reflexivity
 | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
   rewrite U20t; split; [lia|]; split; [lia|]; split;
   [ intros o Ho; cbn [restrict ms_mem mkst]; apply (apresent_writable SEGS);
     apply (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SF + 288 + o) HJ7 ltac:(
       right; right; right; exists 4, pos; split; [left; reflexivity|]; left;
       unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFa6, HFB; lia)))
   | apply Forall_nil ]
 | cbn [ss_mem all_disjoint]; repeat split; (eapply d3_ext; [exact U20t | first [exact U9s | exact U25s] |]); d3_xlia ].
clear SHOK.
(* hw's own shadow (s3+54 = 0, s3+55 = 4: hw_at's block shadow, kept since the start) makes the hw region a
   checked one for the token runner *)
assert (HRAhw : range_addressable (aview SEGS (w_H W5) mem7) SHADOW_OFF (SF + 432) 12).
{ pose proof Hhw as (_ & _ & _ & HBLK). unfold sh_blk, block_shadow, V_hw, N_hw in HBLK.
  destruct HBLK as (_ & _ & HB).
  pose proof (HB 0 ltac:(d3_slim; lia)) as B0. pose proof (HB 1 ltac:(d3_slim; lia)) as B1. clear HB.
  change (0 <? 12 / 8) with true in B0. change (1 <? 12 / 8) with false in B1. change (12 mod 8) with 4 in B1.
  cbv iota in B0, B1.
  assert (Es : shadow_of_addr SHADOW_OFF (SFa g pos + 432) = sh + 54).
  { change (SFa g pos) with SF. rewrite Esh. unfold shadow_of_addr. clear - HSF64. lia. }
  rewrite Es in B0, B1. rewrite Z.add_0_r in B0. replace (sh + 54 + 1) with (sh + 55) in B1 by ring.
  rewrite <- (HKK (sh + 54)) in B0; [| d3_slim; lia | right; right; left; change (shadow_addr SF) with sh; lia
    | unfold d3_wr; d3_xlia].
  rewrite <- (HKK (sh + 55)) in B1; [| d3_slim; lia | right; right; left; change (shadow_addr SF) with sh; lia
    | unfold d3_wr; d3_xlia].
  apply (d3_ra_hw _ SF); [clear - HSF64; lia | exact B0 | exact B1]. }
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (SHOK : sh_ok SEGS d3_Bx [mkSHE 25 0 8; mkSHE 20 144 156] Ex (rd W5 mem7)) end.
{ unfold sh_ok. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_block SEGS B LAWS ly6 S6 W5 mem7 md7 _ d3_Bx 25 pl k 0 8 HAR7 Hinpl6).
    + unfold d3_Bx. apply (U_atom _ 14 SHADOW_OFF); [d3_env; exact G14 | unfold SHADOW_OFF; lia].
    + apply (U_atom _ 25 pl); [d3_env; exact G25 | lia].
    + lia.
    + lia.
  - apply (shent_ok_of_range SEGS (w_H W5) mem7 _ d3_Bx 20 (SF + 432) 12 (SF + 288) 144 156 HRAhw).
    + unfold d3_Bx. apply (U_atom _ 14 SHADOW_OFF); [d3_env; exact G14 | unfold SHADOW_OFF; lia].
    + apply (U_atom _ 20 (SF + 288)); [d3_env; exact G20 | lia].
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. d3_xlia. }
(* ---- run 10: bcmp's result (0x810bc is the branch itself), hw.have = 1, hw.hw = pl[0..8) (to the first shadow
   store 0x81150) ---- *)
psrr_branch_tok RUN BR HS SHOK d3_Bspan.
2: { exfalso. d3_norm Hc. rewrite Hv7, Hv0 in Hc. unfold w64 in Hc. rewrite YO0c.branch_eq in Hc.
     rewrite Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ7 SHOK d3_Bspan.
{ d3_rs.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat (SF + 288)); [reflexivity | d3_env; exact U20 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
    left. unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFa6, HFB; lia. }
  d3_ro. d3_ro. apply awr_ok_nil. }
d3_kkr ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H).
(* ---- the shadow cells of v and ev re-poisoned: a plain run to the join 0x813b4 ---- *)
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (U19f : bv_unsigned (ew Ex 19) = sh) by (d3_env; exact U19);
  assert (U9f : bv_unsigned (ew Ex 9) = mf) by (d3_env; exact U9);
  assert (U20f : bv_unsigned (ew Ex 20) = SF + 288) by (d3_env; exact U20);
  assert (U25f : bv_unsigned (ew Ex 25) = pl) by (d3_env; exact U25) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
  assert (HSa : st_ok_pi SEGS VAL Ex (mkSS (ss_pc ssx) (ss_regs ssx) (d3_sh :: ss_mem ssx) (ss_resv ssx) (ss_facts ssx))
    (restrict (w_H W5) msx)) end.
{ apply st_ok_pi_add_region; [exact HS | reflexivity | |].
  - unfold region_ok, d3_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19f. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. cbn [restrict ms_mem]. apply (apresent_writable SEGS).
    apply (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sh + o) HJ7 ltac:(
      right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
      unfold in_zr; cbn [fst snd]; rewrite EFa6, HFB; change (1024 / 8) with 128; fold sh; lia))).
  - cbn [ss_mem all_disjoint]. repeat split; (eapply d3_ext; [exact U19f | first [exact U20f | exact U9f | exact U25f] |]); d3_xlia. }
clear HS. rename HSa into HS.
paj_run_to_shc RUNTOP HS HJ7 3240.
{ d3_rs.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat sh); [reflexivity | exact U19f | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
    right. unfold in_zr; cbn [fst snd]; rewrite EFa6, HFB; change (1024 / 8) with 128; fold sh; lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat (SF + 288)); [reflexivity | exact U20f | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
    left. unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFa6, HFB; lia. }
  d3_ro. d3_ro. apply awr_ok_nil. }
d3_kkr ltac:(fun H => try rewrite U9 in H; try rewrite U19 in H; try rewrite U20 in H; try rewrite U25 in H).
lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msF) |- _ =>
  pose proof (st_ok_mem_ok SEGS _ _ _ HSx) as HMO; cbn [ss_mem abs_ss setpc ms_mem restrict] in HMO;
  assert (U20g : bv_unsigned (ew Ex 20) = SF + 288) by (d3_env; exact U20);
  pose proof (d3_chunk_val Ex _ _ 20 144 156 144 156 _ 144 4 (SLit 1) 1 HMO ltac:(d3_in) ltac:(d3_in) eq_refl ltac:(d3_slim; lia))
    as VH1;
  pose proof (d3_chunk_val Ex _ _ 20 144 156 144 156 _ 148 4 _
    (RcIdentModel.bz (RcIdentModel.nthb plb 0) + 256 * RcIdentModel.bz (RcIdentModel.nthb plb 1) +
     65536 * RcIdentModel.bz (RcIdentModel.nthb plb 2) + 16777216 * RcIdentModel.bz (RcIdentModel.nthb plb 3))
    HMO ltac:(d3_in) ltac:(d3_in)
    ltac:(rewrite denot_lit_U; f_equal; apply d3_U_le32;
          [d3_env; exact G32 | d3_env; exact G33 | d3_env; exact G34 | d3_env; exact G35
          | exact (RB 0%nat) | exact (RB 1%nat) | exact (RB 2%nat) | exact (RB 3%nat)])
    ltac:(pose proof (RB 0%nat); pose proof (RB 1%nat); pose proof (RB 2%nat); pose proof (RB 3%nat); d3_slim; lia)) as VH2;
  pose proof (d3_chunk_val Ex _ _ 20 144 156 144 156 _ 152 4 _
    (RcIdentModel.bz (RcIdentModel.nthb plb 4) + 256 * RcIdentModel.bz (RcIdentModel.nthb plb 5) +
     65536 * RcIdentModel.bz (RcIdentModel.nthb plb 6) + 16777216 * RcIdentModel.bz (RcIdentModel.nthb plb 7))
    HMO ltac:(d3_in) ltac:(d3_in)
    ltac:(rewrite denot_lit_U; f_equal; apply d3_U_le32;
          [d3_env; exact G36 | d3_env; exact G37 | d3_env; exact G38 | d3_env; exact G39
          | exact (RB 4%nat) | exact (RB 5%nat) | exact (RB 6%nat) | exact (RB 7%nat)])
    ltac:(pose proof (RB 4%nat); pose proof (RB 5%nat); pose proof (RB 6%nat); pose proof (RB 7%nat); d3_slim; lia)) as VH3;
  clear HMO;
  rewrite U20g in VH1, VH2, VH3;
  replace (SF + 288 + 144) with (SF + 432) in VH1 by lia;
  replace (SF + 288 + 148) with (SF + 436) in VH2 by lia;
  replace (SF + 288 + 152) with (SF + 440) in VH3 by lia end.
assert (H8 : (8 <= length plb)%nat).
{ rewrite Hplen. apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. cbn. lia. }
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msF) |- _ =>
  assert (HBY : bytes_at8 W5 (ms_mem msF) (SF + 436) (firstn 8 plb)) end.
{ unfold bytes_at8. rewrite (d3_first8 plb H8).
  change [RcIdentModel.bz (RcIdentModel.nthb plb 0); RcIdentModel.bz (RcIdentModel.nthb plb 1);
          RcIdentModel.bz (RcIdentModel.nthb plb 2); RcIdentModel.bz (RcIdentModel.nthb plb 3);
          RcIdentModel.bz (RcIdentModel.nthb plb 4); RcIdentModel.bz (RcIdentModel.nthb plb 5);
          RcIdentModel.bz (RcIdentModel.nthb plb 6); RcIdentModel.bz (RcIdentModel.nthb plb 7)]
    with ([RcIdentModel.bz (RcIdentModel.nthb plb 0); RcIdentModel.bz (RcIdentModel.nthb plb 1);
           RcIdentModel.bz (RcIdentModel.nthb plb 2); RcIdentModel.bz (RcIdentModel.nthb plb 3)] ++
          [RcIdentModel.bz (RcIdentModel.nthb plb 4); RcIdentModel.bz (RcIdentModel.nthb plb 5);
           RcIdentModel.bz (RcIdentModel.nthb plb 6); RcIdentModel.bz (RcIdentModel.nthb plb 7)]).
  apply (d3_garr8_app' _ _ _ (SF + 440)).
  - apply d3_vm4_bytes; [exact (RB 0%nat) | exact (RB 1%nat) | exact (RB 2%nat) | exact (RB 3%nat) | exact VH2].
  - cbn [length]. lia.
  - apply d3_vm4_bytes; [exact (RB 4%nat) | exact (RB 5%nat) | exact (RB 6%nat) | exact (RB 7%nat) | exact VH3]. }
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msF),
    HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msF) _ _ |- _ =>
  prreg HSx (2%bv : bv 5) F2; prreg HSx (3%bv : bv 5) F3; prreg HSx (4%bv : bv 5) F4; prreg HSx (8%bv : bv 5) F8;
  prreg HSx (9%bv : bv 5) F9; prreg HSx (19%bv : bv 5) F19; prreg HSx (21%bv : bv 5) F21; prreg HSx (22%bv : bv 5) F22;
  prreg HSx (24%bv : bv 5) F24; prreg HSx (25%bv : bv 5) F25; prreg HSx (26%bv : bv 5) F26;
  pmkst HSx; apply SRr_ret;
  apply (d3_finish g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ _ _ _ _ _ HJs Hfrs Hk MLE MOK HC (proj1 HP) Hhw Hr1 Hav HJx Hfr6
    Hperm6 HKK VH1 HBY)
end.
- rewrite F2. exact (EE 2%nat 2%bv eq_refl).
- rewrite F9. exact (EE 9%nat 9%bv eq_refl).
- rewrite F8. exact (EE 8%nat 8%bv eq_refl).
- rewrite F3. exact (EE 3%nat 3%bv eq_refl).
- rewrite F4. exact (EE 4%nat 4%bv eq_refl).
- rewrite F19. exact (EE 19%nat 19%bv eq_refl).
- rewrite F22. exact (EE 22%nat 22%bv eq_refl).
- rewrite F26. exact G40.
- rewrite F24. rewrite U20. unfold V_before, w64. change (SFa g pos) with SF. f_equal. lia.
- rewrite F25. exact G25.
- rewrite F21. exact G41.
Qed.

End c.
End b.
End a.
