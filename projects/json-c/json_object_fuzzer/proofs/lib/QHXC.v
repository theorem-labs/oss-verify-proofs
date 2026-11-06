(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qio9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qio9.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.

Lemma unsigned_Z_to_bv_sub_r : forall e d, Z_to_bv 64 (d - bv_unsigned (Z_to_bv 64 e)) = Z_to_bv 64 (d - e).
Proof.
intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zminus_mod_idemp_r. reflexivity.
Qed.
Lemma den_add_wl : forall (a : word) k, alu64 ALU_ADD a (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned a + k).
Proof. intros. rewrite alu_add. unfold v_add. apply unsigned_Z_to_bv_add_r. Qed.
Lemma den_add_zl : forall a k, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a + k).
Proof. intros. rewrite den_add_wl. apply unsigned_Z_to_bv_add. Qed.
Lemma den_add_ww : forall (a b : word), alu64 ALU_ADD a b = Z_to_bv 64 (bv_unsigned a + bv_unsigned b).
Proof. intros. rewrite alu_add. reflexivity. Qed.
Lemma den_sub_wl : forall (a : word) k, alu64 ALU_SUB a (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned a - k).
Proof. intros. rewrite alu_sub. unfold v_sub. apply unsigned_Z_to_bv_sub_r. Qed.
Lemma u64_of_Z : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply u_small. assumption. Qed.
Lemma s64_of_Z : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
Lemma swrap32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 / 2)%Z with (2^31)%Z. lia. Qed.
Lemma Z_to_bv_of_word : forall (a : word), Z_to_bv 64 (bv_unsigned a) = a.
Proof. intros. apply Z_to_bv_bv_unsigned. Qed.
Lemma Z_to_bv_add0 : forall (a : word), Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intros. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64).
assert (D : Z.ldiff x (Z.ones 64) = 0).
{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by (unfold Z.ones; cbn; lia). reflexivity. }
pose proof (Z.sub_nocarry_ldiff (Z.ones 64) x D) as S.
assert (L : Z.land (Z.ones 64 - x) x = 0).
{ rewrite S. rewrite Z.ldiff_land. rewrite <- Z.land_assoc. rewrite (Z.land_comm (Z.lnot x) x). rewrite Z.land_lnot_diag. apply Z.land_0_r. }
pose proof (Z.add_nocarry_lxor _ _ L) as A.
replace (Z.ones 64 - x + x) with (Z.ones 64) in A by lia.
apply (f_equal (fun z => Z.lxor z x)) in A. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r in A.
rewrite Z.lxor_comm. exact A.
Qed.
Lemma den_not : forall x : word, alu64 ALU_XOR x (Z_to_bv 64 (-1)) = Z_to_bv 64 (18446744073709551615 - bv_unsigned x).
Proof.
intros x. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
rewrite alu_xor. unfold v_xor.
change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615. rewrite lxor_ones64 by lia. reflexivity.
Qed.

Lemma den_sub_lin : forall a b : word,
alu64 ALU_ADD a (mul_div M_MUL (Z_to_bv 64 (-1)) b) = Z_to_bv 64 (bv_unsigned a - bv_unsigned b).
Proof.
intros a b. pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 b).
rewrite alu_add. unfold v_add.
change (mul_div M_MUL (Z_to_bv 64 (-1)) b) with (bv_mul (Z_to_bv 64 (-1)) b).
apply bv_eq. rewrite !Z_to_bv_unsigned, bv_mul_unsigned. change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615.
unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Zplus_mod_idemp_r.
replace (bv_unsigned a + 18446744073709551615 * bv_unsigned b) with ((bv_unsigned a - bv_unsigned b) + bv_unsigned b * 2^64) by lia.
apply Z_mod_plus_full.
Qed.

Lemma den_sub_lin2 : forall a b : word,
alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) b) a = Z_to_bv 64 (bv_unsigned a - bv_unsigned b).
Proof.
intros a b. rewrite <- den_sub_lin. rewrite alu_add. rewrite (alu_add a). unfold v_add. f_equal. apply Z.add_comm.
Qed.

Definition nthe (sr : list expr) (i : nat) : expr := nth i sr (ELit 0).

Lemma regs_ok_mkR : forall E sr
x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
length sr = 32%nat ->
edenot E (nthe sr 1) = x1 -> edenot E (nthe sr 2) = x2 -> edenot E (nthe sr 3) = x3 -> edenot E (nthe sr 4) = x4 ->
edenot E (nthe sr 5) = x5 -> edenot E (nthe sr 6) = x6 -> edenot E (nthe sr 7) = x7 -> edenot E (nthe sr 8) = x8 ->
edenot E (nthe sr 9) = x9 -> edenot E (nthe sr 10) = x10 -> edenot E (nthe sr 11) = x11 -> edenot E (nthe sr 12) = x12 ->
edenot E (nthe sr 13) = x13 -> edenot E (nthe sr 14) = x14 -> edenot E (nthe sr 15) = x15 -> edenot E (nthe sr 16) = x16 ->
edenot E (nthe sr 17) = x17 -> edenot E (nthe sr 18) = x18 -> edenot E (nthe sr 19) = x19 -> edenot E (nthe sr 20) = x20 ->
edenot E (nthe sr 21) = x21 -> edenot E (nthe sr 22) = x22 -> edenot E (nthe sr 23) = x23 -> edenot E (nthe sr 24) = x24 ->
edenot E (nthe sr 25) = x25 -> edenot E (nthe sr 26) = x26 -> edenot E (nthe sr 27) = x27 -> edenot E (nthe sr 28) = x28 ->
edenot E (nthe sr 29) = x29 -> edenot E (nthe sr 30) = x30 -> edenot E (nthe sr 31) = x31 ->
regs_ok E sr (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof.
intros E sr x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HL.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31.
intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
- pose proof (ridx_range r) as Hlt.
rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
unfold nthe in *.
set (n := ridx r) in *. clearbody n.
do 32 (destruct n as [|n]; [vm_compute in Hr0; first [discriminate | symmetry; assumption] |]).
exfalso. lia.
Qed.

Section Kn.
Variable segs : list Segment.

#[using="Type"] Lemma rdn_is_ov : forall m a n, QsjA.rdn segs m a n = ov_read_bytes segs m a n.
Proof. intros. symmetry. apply QsjA.ov_rdn. Qed.

#[using="Type"] Lemma kword_of_cells : forall E m (e : expr) (a : word) (d : Z) A cs k c w (v : expr) (x : word),
cells_at segs m A cs -> cell_at cs k = Some c ->
edenot E e = a -> A = bv_unsigned a + d ->
csize c = w -> cbytes c = word_to_le_bytes w x -> edenot E v = x -> (1 <= w <= 8)%nat ->
kentry_ok segs E m (KWord (SA e (d + Z.of_nat k)) w v).
Proof.
intros E m e a d A cs k c w v x HC Hk He HA Hw Hb Hv Hw8.
pose proof (cells_at_bound segs m A cs HC) as [HA0 HA1].
pose proof (cell_at_bound cs k c Hk) as Hkb.
eapply kword_intro; [exact He | exact Hv | lia | lia | lia | lia |].
rewrite rdn_is_ov. rewrite <- Hb, <- Hw.
replace (Z_to_bv 64 (bv_unsigned a + (d + Z.of_nat k))) with (wa (A + Z.of_nat k)) by (unfold wa; f_equal; lia).
eapply cells_at_read; eassumption.
Qed.

#[using="Type"] Lemma kword_of_rw : forall E m (e : expr) (a : word) (d : Z) A cs k c w (v : expr) (x : word),
rw_cells segs m A cs -> cell_at cs k = Some c ->
edenot E e = a -> A = bv_unsigned a + d ->
csize c = w -> cbytes c = word_to_le_bytes w x -> edenot E v = x -> (1 <= w <= 8)%nat ->
kentry_ok segs E m (KWord (SA e (d + Z.of_nat k)) w v).
Proof. intros E m e a d A cs k c w v x HR. destruct HR as [HC HW]. intros; eapply kword_of_cells; eassumption. Qed.

#[using="Type"] Lemma kword_of_ro : forall E m (e : expr) (a : word) (d : Z) A cs k c w (v : expr) (x : word),
ro_cells segs m A cs -> cell_at cs k = Some c ->
edenot E e = a -> A = bv_unsigned a + d ->
csize c = w -> cbytes c = word_to_le_bytes w x -> edenot E v = x -> (1 <= w <= 8)%nat ->
kentry_ok segs E m (KWord (SA e (d + Z.of_nat k)) w v).
Proof. intros E m e a d A cs k c w v x HC. intros; eapply kword_of_cells; eassumption. Qed.

#[using="Type"] Lemma kword_of_bytes_at : forall E m (e : expr) (a : word) (d : Z) A bs w (v : expr) (x : word),
bytes_at segs m A bs -> bs = word_to_le_bytes w x ->
edenot E e = a -> A = bv_unsigned a + d -> edenot E v = x -> (1 <= w <= 8)%nat ->
kentry_ok segs E m (KWord (SA e d) w v).
Proof.
intros E m e a d A bs w v x HB Hbs He HA Hv Hw.
assert (HL : length bs = w) by (rewrite Hbs; unfold word_to_le_bytes; apply length_Z_to_le_bytes).
destruct HB as (HA0 & HA1 & HR0).
eapply kword_intro; [exact He | exact Hv | lia | lia | lia | lia |].
rewrite rdn_is_ov, <- HA.
pose proof (bytes_at_ov_read segs m A bs 0 w (conj HA0 (conj HA1 HR0)) ltac:(lia)) as R.
rewrite Z.add_0_r in R. unfold wa in R. rewrite R. cbn [skipn]. f_equal. subst bs. rewrite <- HL at 1. apply firstn_all.
Qed.

#[using="Type"] Lemma cbytes_C8 : forall v, cbytes (C8 v) = word_to_le_bytes 8 v. Proof. reflexivity. Qed.
#[using="Type"] Lemma cbytes_C4 : forall v, cbytes (C4 v) = word_to_le_bytes 4 v. Proof. reflexivity. Qed.
#[using="Type"] Lemma cbytes_C2 : forall v, cbytes (C2 v) = word_to_le_bytes 2 v. Proof. reflexivity. Qed.
#[using="Type"] Lemma cbytes_C1 : forall (b : byte), cbytes (C1 b) = word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b)).
Proof.
intros b. cbn [cbytes word_to_le_bytes Z_to_le_bytes]. f_equal. apply bv_eq.
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb.
rewrite u_small by lia. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply (bv_unsigned_in_range 8 b).
Qed.

#[using="Type"] Lemma kwr_of_rw : forall E m (e : expr) (a : word) (d : Z) A cs n,
rw_cells segs m A cs -> edenot E e = a -> A = bv_unsigned a + d -> n = Z.of_nat (cells_size cs) -> 0 < n ->
kentry_ok segs E m (KWr (SA e d) n).
Proof.
intros E m e a d A cs n HR He HA Hn Hn0. destruct HR as [HC HW]. cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off].
rewrite He. pose proof (cells_at_bound segs m A cs HC) as [HA0 HA1]. pose proof (u64_range a).
split; [lia|]. intros dd mm Hd Hm.
replace (Z_to_bv 64 (bv_unsigned a + d + dd)) with (wa (A + dd)) by (unfold wa; f_equal; lia).
eapply wr_at_store_ok; [exact HW | lia | lia].
Qed.

#[using="Type"] Lemma kwr_of_stk : forall E m (e : expr) (a : word) lo hi d n,
stk segs m lo hi -> edenot E e = a ->
lo <= bv_unsigned a + d -> 0 < n -> bv_unsigned a + d + n <= hi ->
kentry_ok segs E m (KWr (SA e d) n).
Proof.
intros E m e a lo hi d n HS0 He H1 H2 H3. destruct HS0 as (Hlo & Hhi & HS). cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off].
rewrite He. pose proof (u64_range a). split; [lia|]. intros dd mm Hd Hm.
assert (W : wr_at segs m (bv_unsigned a + d) n).
{ split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (HS (bv_unsigned a + d + i) ltac:(lia))). }
replace (Z_to_bv 64 (bv_unsigned a + d + dd)) with (wa (bv_unsigned a + d + dd)) by reflexivity.
eapply wr_at_store_ok; [exact W | lia | lia].
Qed.

Fixpoint ro_cover (sl : list Segment) (lo hi : Z) : bool :=
match sl with
| [] => false
| s :: rest =>
let base := Z.of_N (seg_base s) in
let top := base + Z.of_N (seg_size s) in
if (base <=? lo) && (hi <=? top) then negb (seg_writable s)
else ((top <=? lo) || (hi <=? base)) && ro_cover rest lo hi
end.

#[using="Type"] Lemma ro_cover_find : forall sl lo hi i,
ro_cover sl lo hi = true -> lo <= i < hi ->
exists s, find_segment sl i 1 = Some s /\ seg_writable s = false.
Proof.
induction sl as [|s rest IH]; intros lo hi i H Hi; cbn in H; [discriminate|].
cbn [find_segment].
destruct ((Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:C.
- apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
exists s. replace ((Z.of_N (seg_base s) <=? i) && (i + 1 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with true
by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
split; [reflexivity|]. destruct (seg_writable s); [discriminate H | reflexivity].
- apply andb_true_iff in H as [D H].
replace ((Z.of_N (seg_base s) <=? i) && (i + 1 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
+ eapply IH; eassumption.
+ symmetry. apply andb_false_iff. apply orb_true_iff in D as [D|D]; apply Z.leb_le in D;
[right | left]; apply Z.leb_gt; lia.
Qed.

#[using="Type"] Lemma kimg_of_mem_inv : forall E m lo hi,
mem_inv segs m -> ro_cover segs lo hi = true -> 0 <= lo -> hi <= 2^64 ->
kentry_ok segs E m (KImg lo hi).
Proof.
intros E m lo hi HM HC H0 H1. apply kimg_intro; [lia | lia |].
intros i Hi. destruct (m (Z_to_bv 64 i)) as [b|] eqn:Em; [|reflexivity].
exfalso. pose proof (HM _ _ Em) as R. unfold ro_addr in R.
rewrite u_small in R by lia.
destruct (ro_cover_find segs lo hi i HC Hi) as (s & Hs & Hw). rewrite Hs, Hw in R. discriminate R.
Qed.

#[using="Type"] Lemma krange_of : forall E m (e : expr) (a : word) lo hi,
edenot E e = a -> lo <= bv_unsigned a <= hi -> kentry_ok segs E m (KRange e lo hi).
Proof. intros E m e a lo hi <- H. apply krange_intro. exact H. Qed.

#[using="Type"] Lemma kalign_of : forall E m (e : expr) (a : word) k,
edenot E e = a -> 0 < k -> bv_unsigned a mod k = 0 -> kentry_ok segs E m (KAlign e k).
Proof. intros E m e a k <- Hk H. apply kalign_intro; assumption. Qed.

#[using="Type"] Lemma sc_readbase_byte : forall m A bs k (b : byte) (a : word),
bytes_at segs m A bs -> nth_error bs k = Some b -> a = Z_to_bv 64 (A + Z.of_nat k) ->
exists bs', QsjA.rdn segs m a 1 = Some bs' /\ Z_to_bv 64 (extz false 1 (bytes_le_to_Z bs')) = Z_to_bv 64 (bv_unsigned b).
Proof.
intros m A bs k b a HB Hk ->. exists [b]. split.
- rewrite rdn_is_ov. pose proof (proj1 (nth_error_Some bs k) ltac:(rewrite Hk; discriminate)) as Hl.
change (Z_to_bv 64 (A + Z.of_nat k)) with (wa (A + Z.of_nat k)).
rewrite (bytes_at_ov_read segs m A bs k 1 HB ltac:(lia)).
f_equal. rewrite <- (firstn_skipn k bs) in Hk. rewrite nth_error_app2 in Hk by (rewrite length_firstn; lia).
rewrite length_firstn in Hk. replace (k - Nat.min k (length bs))%nat with 0%nat in Hk by lia.
destruct (skipn k bs) as [|b' r]; cbn in Hk; [discriminate|]. injection Hk as ->. reflexivity.
- cbn [extz bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

#[using="Type"] Lemma sc_readbase_byte_sx : forall m A bs k (b : byte) (a : word),
bytes_at segs m A bs -> nth_error bs k = Some b -> a = Z_to_bv 64 (A + Z.of_nat k) -> bv_unsigned b < 128 ->
exists bs', QsjA.rdn segs m a 1 = Some bs' /\ Z_to_bv 64 (extz true 1 (bytes_le_to_Z bs')) = Z_to_bv 64 (bv_unsigned b).
Proof.
intros m A bs k b a HB Hk Ha Hb.
destruct (sc_readbase_byte m A bs k b a HB Hk Ha) as (bs' & H1 & H2). exists bs'. split; [exact H1|].
revert H2. cbn [extz]. intros H2.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
pose proof (bytes_le_to_Z_bound bs') as B.
rewrite (QsjA.rdn_length segs m 1 a bs' H1) in B. cbn in B.
assert (E1 : bytes_le_to_Z bs' = bv_unsigned b).
{ apply (f_equal bv_unsigned) in H2. rewrite !u_small in H2; [exact H2 | lia | lia]. }
rewrite E1. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N (8 * N.of_nat 1))%Z with 256%Z. f_equal.
rewrite Z.mod_small by lia. lia.
Qed.
End Kn.
