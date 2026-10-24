(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m YP0e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e.
Variable segs : list Segment.
Definition mbyte (m : word -> option byte) (a : Z) : option byte :=
match m (Z_to_bv 64 a) with
| Some b => Some b
| None => seg_rom segs (Z_to_bv 64 a)
end.
Lemma Z_to_bv64_add1 : forall a, (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1).
Proof.
intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
change (bv_unsigned (1 : word)) with 1.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma rdn_mbytes : forall m n a bs,
rdn segs m (Z_to_bv 64 a) n = Some bs <->
(length bs = n /\ forall i, (i < n)%nat -> mbyte m (a + Z.of_nat i) = nth_error bs i).
Proof.
intros m n. induction n as [|n IH]; intros a bs.
- cbn. split.
+ intros H. injection H as <-. split; [reflexivity|]. intros i Hi. lia.
+ intros [Hl _]. destruct bs; [reflexivity|discriminate].
- cbn [rdn]. fold (mbyte m a).
change (match m (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end)
with (mbyte m a).
rewrite Z_to_bv64_add1.
destruct (mbyte m a) as [b|] eqn:Hb.
+ destruct (rdn segs m (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Hr.
* split.
-- intros H. injection H as <-. apply IH in Hr as [Hlen Hr].
split; [cbn; lia|]. intros i Hi. destruct i as [|i]; [cbn; rewrite Z.add_0_r; exact Hb|].
cbn. rewrite <- Hr by lia. f_equal. lia.
-- intros [Hlen H]. destruct bs as [|b' rest']; [discriminate|].
pose proof (H 0%nat ltac:(lia)) as H0. cbn in H0. rewrite Z.add_0_r in H0.
rewrite Hb in H0. injection H0 as ->. f_equal.
assert (Hr' : rdn segs m (Z_to_bv 64 (a + 1)) n = Some rest').
{ apply IH. split; [cbn in Hlen; lia|]. intros i Hi.
specialize (H (S i) ltac:(lia)). cbn in H. rewrite <- H. f_equal. lia. }
congruence.
* split; [discriminate|]. intros [Hlen H]. exfalso.
destruct bs as [|b' rest']; [discriminate|].
assert (Hr' : rdn segs m (Z_to_bv 64 (a + 1)) n = Some rest').
{ apply IH. split; [cbn in Hlen; lia|]. intros i Hi.
specialize (H (S i) ltac:(lia)). cbn in H. rewrite <- H. f_equal. lia. }
congruence.
+ split; [discriminate|]. intros [Hlen H]. exfalso.
destruct bs as [|b' rest']; [discriminate|].
specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r, Hb in H. discriminate.
Qed.
Lemma wbytes_mbyte : forall bs m a x,
0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> 0 <= x < 2^64 ->
mbyte (wbytes m (Z_to_bv 64 a) bs) x =
if (a <=? x) && (x <? a + Z.of_nat (length bs))
then nth_error bs (Z.to_nat (x - a)) else mbyte m x.
Proof.
induction bs as [|b rest IH]; intros m a x Ha Hnw Hx.
- cbn [wbytes length Z.of_nat]. rewrite Z.add_0_r.
destruct (a <=? x) eqn:H1; cbn [andb]; [|reflexivity].
destruct (x <? a) eqn:H2; [apply Z.ltb_lt in H2; apply Z.leb_le in H1; lia| reflexivity].
- cbn [wbytes length]. rewrite Z_to_bv64_add1.
cbn [length] in Hnw.
rewrite IH by lia.
rewrite Nat2Z.inj_succ in *.
destruct (Z.eq_dec x a) as [->|Hne].
+ replace ((a + 1 <=? a) && (a <? a + 1 + Z.of_nat (length rest))) with false
by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
replace ((a <=? a) && (a <? a + Z.succ (Z.of_nat (length rest)))) with true
by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
rewrite Z.sub_diag. cbn. unfold mbyte. rewrite bv_eqb_refl. reflexivity.
+ assert (Hneb : bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 a) = false).
{ apply bv_eqb_false_iff. intros Heq. apply (f_equal bv_unsigned) in Heq.
rewrite !Z_to_bv_unsigned, !bv_wrap_small in Heq by (change (bv_modulus 64) with (2^64); lia).
lia. }
destruct ((a + 1 <=? x) && (x <? a + 1 + Z.of_nat (length rest))) eqn:Hin.
* apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
replace ((a <=? x) && (x <? a + Z.succ (Z.of_nat (length rest)))) with true
by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
replace (Z.to_nat (x - a)) with (S (Z.to_nat (x - (a + 1)))) by lia. reflexivity.
* replace ((a <=? x) && (x <? a + Z.succ (Z.of_nat (length rest)))) with false.
2:{ symmetry. apply andb_false_iff.
apply andb_false_iff in Hin. destruct Hin as [H1|H2].
- apply Z.leb_gt in H1. left. apply Z.leb_gt. lia.
- apply Z.ltb_ge in H2. right. apply Z.ltb_ge. lia. }
unfold mbyte. rewrite Hneb. reflexivity.
Qed.
Inductive cval : Type :=
| CVal (w : N) (v : sv)
| CZero (len : Z)
| CImg (len : Z)
| CData (d : nat) (s : Z) (len : Z).
Record chunk := mkChunk { c_off : Z; c_val : cval }.
Definition cv_len (cv : cval) : Z :=
match cv with
| CVal w _ => Z.of_N w
| CZero l => l
| CImg l => l
| CData _ _ l => l
end.
Definition c_len (c : chunk) : Z := cv_len (c_val c).
Record region := mkRegion {
r_base : option nat;
r_lo : Z; r_hi : Z;
r_wlo : Z; r_whi : Z;
r_chunks : list chunk
}.
Definition smem := list region.
Definition base_val (E : env) (b : option nat) : Z :=
match b with Some n => bv_unsigned (ew E n) | None => 0 end.
Definition byte_of_word (w : word) (i : Z) : byte :=
Z_to_bv 8 (Z.shiftr (bv_unsigned w) (8 * i)).
Definition img_byte (a : Z) : option byte := seg_rom segs (Z_to_bv 64 a).
Definition cbyte (E : env) (abs_addr : Z) (cv : cval) (i : Z) : option byte :=
match cv with
| CVal _ v => Some (byte_of_word (sv_denot E v) i)
| CZero _ => Some (Z_to_bv 8 0)
| CImg _ => img_byte (abs_addr + i)
| CData d s _ => nth_error (ed E d) (Z.to_nat (s + i))
end.
Definition chunk_ok (E : env) (m : word -> option byte) (base : Z) (c : chunk) : Prop :=
forall i, 0 <= i < c_len c ->
exists b, cbyte E (base + c_off c) (c_val c) i = Some b /\ mbyte m (base + c_off c + i) = Some b.
Definition writable_at (m : word -> option byte) (a : Z) : Prop :=
wview segs m (Z_to_bv 64 a) <> None.
Definition region_ok (E : env) (m : word -> option byte) (r : region) : Prop :=
let base := base_val E (r_base r) in
0 <= base + r_lo r /\ base + r_hi r <= 2^64
/\ (forall o, r_wlo r <= o < r_whi r -> writable_at m (base + o))
/\ Forall (chunk_ok E m base) (r_chunks r).
Definition chunk_inside (r : region) (c : chunk) : bool :=
(r_lo r <=? c_off c) && (c_off c + c_len c <=? r_hi r) && (0 <=? c_len c).
Definition region_wf (r : region) : bool :=
(r_lo r <=? r_hi r)
&& ((r_whi r <=? r_wlo r) || ((r_lo r <=? r_wlo r) && (r_whi r <=? r_hi r)))
&& forallb (chunk_inside r) (r_chunks r).
Fixpoint regions_wf (rs : smem) : bool :=
match rs with [] => true | r :: rs' => region_wf r && regions_wf rs' end.
Definition extent_disjoint (E : env) (r1 r2 : region) : Prop :=
base_val E (r_base r1) + r_hi r1 <= base_val E (r_base r2) + r_lo r2
\/ base_val E (r_base r2) + r_hi r2 <= base_val E (r_base r1) + r_lo r1.
Fixpoint all_disjoint (E : env) (r : region) (rs : smem) : Prop :=
match rs with [] => True | r' :: rs' => extent_disjoint E r r' /\ all_disjoint E r rs' end.
Fixpoint pairwise_disjoint (E : env) (rs : smem) : Prop :=
match rs with [] => True | r :: rs' => all_disjoint E r rs' /\ pairwise_disjoint E rs' end.
Definition mem_ok (E : env) (m : word -> option byte) (rs : smem) : Prop :=
regions_wf rs = true /\ Forall (region_ok E m) rs /\ pairwise_disjoint E rs.
Definition obase_eqb (a b : option nat) : bool :=
match a, b with
| None, None => true
| Some x, Some y => Nat.eqb x y
| _, _ => false
end.
Fixpoint find_region (rs : smem) (b : option nat) (off n : Z) : option region :=
match rs with
| [] => None
| r :: rs' => if obase_eqb (r_base r) b && (r_lo r <=? off) && (off + n <=? r_hi r)
then Some r else find_region rs' b off n
end.
Fixpoint find_chunk (cs : list chunk) (off n : Z) : option chunk :=
match cs with
| [] => None
| c :: cs' => if (c_off c <=? off) && (off + n <=? c_off c + c_len c)
then Some c else find_chunk cs' off n
end.
Fixpoint img_bytes (a : Z) (n : nat) : option (list byte) :=
match n with
| O => Some []
| S n' => match img_byte a, img_bytes (a + 1) n' with
| Some b, Some r => Some (b :: r)
| _, _ => None
end
end.
Definition nbytes (sz : msize) : nat :=
match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end%nat.
Definition nbits (sz : msize) : N :=
match sz with SZ1 => 8 | SZ2 => 16 | SZ4 => 32 | SZ8 => 64 end%N.
Definition loadres (G : facts) (sz : msize) (sg : bool) (raw : sv) : sv :=
match sz with
| SZ8 => raw
| _ => s_ext2 G sg (nbits sz) raw
end.
Definition sload (G : facts) (rs : smem) (b : option nat) (off : Z) (sz : msize) (sg : bool)
: option sv :=
let n := Z.of_nat (nbytes sz) in
match find_region rs b off n with
| None => None
| Some r =>
match find_chunk (r_chunks r) off n with
| None => None
| Some c =>
let k := off - c_off c in
match c_val c with
| CVal w v =>
if negb (Z.of_N w <=? 8) then None
else if (k =? 0) then Some (loadres G sz sg v)
else Some (loadres G sz sg (s_alu G ALU_SRL v (SLit (8 * k))))
| CZero _ => Some (SLit 0)
| CImg _ =>
match b with
| None => match img_bytes (off) (nbytes sz) with
| Some bs => Some (loadres G sz sg (SLit (bytes_le_to_Z bs)))
| None => None
end
| Some _ => None
end
| CData d s _ => if 0 <=? s then Some (loadres G sz sg (SData d (s + k) (N.of_nat (nbytes sz))))
else None
end
end
end.
Fixpoint cut_chunks (cs : list chunk) (off n : Z) : list chunk :=
match cs with
| [] => []
| c :: cs' =>
let rest := cut_chunks cs' off n in
let co := c_off c in let cl := c_len c in
if (co + cl <=? off) || (off + n <=? co) then c :: rest
else
let left := if co <? off then
match c_val c with
| CZero _ => [mkChunk co (CZero (off - co))]
| CImg _ => [mkChunk co (CImg (off - co))]
| CData d s _ => [mkChunk co (CData d s (off - co))]
| CVal _ _ => []
end else [] in
let right := if off + n <? co + cl then
match c_val c with
| CZero _ => [mkChunk (off + n) (CZero (co + cl - (off + n)))]
| CImg _ => [mkChunk (off + n) (CImg (co + cl - (off + n)))]
| CData d s _ => [mkChunk (off + n) (CData d (s + (off + n - co)) (co + cl - (off + n)))]
| CVal _ _ => []
end else [] in
left ++ right ++ rest
end.
Fixpoint store_region (rs : smem) (b : option nat) (off : Z) (n : Z) (cv : cval) : option smem :=
match rs with
| [] => None
| r :: rs' =>
if obase_eqb (r_base r) b && (r_lo r <=? off) && (off + n <=? r_hi r) then
if (r_wlo r <=? off) && (off + n <=? r_whi r) then
Some (mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r)
(mkChunk off cv :: cut_chunks (r_chunks r) off n) :: rs')
else None
else match store_region rs' b off n cv with
| Some rs'' => Some (r :: rs'')
| None => None
end
end.
Definition sstore (rs : smem) (b : option nat) (off : Z) (sz : msize) (v : sv) : option smem :=
store_region rs b off (Z.of_nat (nbytes sz)) (CVal (N.of_nat (nbytes sz)) v).
Fixpoint zbytes (z : Z) (k : Z) (n : nat) : list byte :=
match n with
| O => []
| S n' => Z_to_bv 8 (Z.shiftr z (8 * k)) :: zbytes z (k + 1) n'
end.
Lemma length_zbytes : forall z k n, length (zbytes z k n) = n.
Proof. intros z k n. revert k. induction n; intros; cbn; auto. Qed.
Lemma testbit_bytes_le_cons : forall (b : byte) rest i, 0 <= i ->
Z.testbit (bytes_le_to_Z (b :: rest)) i =
if i <? 8 then Z.testbit (bv_unsigned b) i else Z.testbit (bytes_le_to_Z rest) (i - 8).
Proof.
intros b rest i Hi. cbn [bytes_le_to_Z]. rewrite Z.lor_spec.
pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with (2^8) in Hb.
destruct (i <? 8) eqn:Hlt.
- apply Z.ltb_lt in Hlt. rewrite Z.shiftl_spec_low by lia. apply orb_false_r.
- apply Z.ltb_ge in Hlt. rewrite Z.shiftl_spec_high by lia.
rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.
Lemma zbytes_spec : forall n z k, 0 <= z -> 0 <= k ->
bytes_le_to_Z (zbytes z k n) = (Z.shiftr z (8 * k)) mod 2 ^ (8 * Z.of_nat n).
Proof.
induction n as [|n IH]; intros z k Hz Hk.
- cbn. rewrite Z.mod_1_r. reflexivity.
- cbn [zbytes]. apply Z.bits_inj'. intros i Hi.
rewrite testbit_bytes_le_cons by lia.
rewrite IH by lia.
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (z ≫ (8 * k))) with ((z ≫ (8 * k)) mod 2^8).
replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia.
destruct (i <? 8) eqn:Hlt.
+ apply Z.ltb_lt in Hlt.
rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
+ apply Z.ltb_ge in Hlt.
destruct (Z_lt_le_dec (i - 8) (8 * Z.of_nat n)).
* rewrite !Z.mod_pow2_bits_low by lia.
rewrite !Z.shiftr_spec by lia. f_equal. lia.
* rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Definition st_bytes (n : nat) (w : word) : list byte := zbytes (bv_unsigned w) 0 n.
Lemma Z_to_le_bytes_zbytes : forall n z k,
Z_to_le_bytes n (Z.shiftr z (8 * k)) = zbytes z k n.
Proof.
induction n as [|n IH]; intros z k; [reflexivity|].
cbn [Z_to_le_bytes zbytes]. f_equal.
rewrite <- IH. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma Z_to_le_bytes_st : forall n (w : word),
Z_to_le_bytes n (bv_unsigned w) = st_bytes n w.
Proof.
intros n w. unfold st_bytes. rewrite <- (Z_to_le_bytes_zbytes n (bv_unsigned w) 0).
rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
Qed.
Lemma zbytes_mod : forall n z k m, 0 <= k -> 8 * (k + Z.of_nat n) <= m ->
zbytes (z mod 2 ^ m) k n = zbytes z k n.
Proof.
induction n as [|n IH]; intros z k m Hk Hm; [reflexivity|].
cbn [zbytes]. f_equal.
- apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with (2^8).
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8).
+ rewrite !Z.mod_pow2_bits_low, !Z.shiftr_spec, Z.mod_pow2_bits_low by lia. reflexivity.
+ rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
- apply IH; lia.
Qed.
Lemma nth_error_zbytes : forall n z k i, (i < n)%nat ->
nth_error (zbytes z k n) i = Some (Z_to_bv 8 (Z.shiftr z (8 * (k + Z.of_nat i)))).
Proof.
induction n as [|n IH]; intros z k i Hi; [lia|].
destruct i as [|i]; cbn [zbytes nth_error].
- f_equal. f_equal. f_equal. lia.
- rewrite IH by lia. f_equal. f_equal. f_equal. lia.
Qed.
Definition load_result (sz : msize) (sg : bool) (raw : word) : word :=
match sz with
| SZ8 => raw
| _ => if sg then sext 64 (bv_extract 0 (nbits sz) raw) else zext 64 (bv_extract 0 (nbits sz) raw)
end.
Lemma nbits_nbytes : forall sz, Z.of_N (nbits sz) = 8 * Z.of_nat (nbytes sz).
Proof. destruct sz; reflexivity. Qed.
Lemma bv_extract0_mod : forall (w : N) z, (Z.of_N w <= 64) ->
bv_extract 0 w (Z_to_bv 64 (z mod 2 ^ Z.of_N w)) = bv_extract 0 w (Z_to_bv 64 z).
Proof.
intros w z Hw. apply bv_eq.
rewrite !bv_extract_unsigned, !Z.shiftr_0_r, !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2^64). unfold bv_modulus.
pose proof (N2Z.is_nonneg w) as Hw0.
rewrite (Z.mod_small (z mod 2 ^ Z.of_N w) (2^64)).
2:{ pose proof (Z.mod_pos_bound z (2 ^ Z.of_N w) ltac:(apply Z.pow_pos_nonneg; lia)).
assert (2 ^ Z.of_N w <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia. }
rewrite Z.mod_mod by (apply Z.pow_nonzero; lia).
symmetry. apply Z.mod_mod_divide.
exists (2 ^ (64 - Z.of_N w)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma loadres_sound : forall E G sz sg rawv z,
facts_ok E G ->
sv_denot E rawv = Z_to_bv 64 z ->
sv_denot E (loadres G sz sg rawv) = load_result sz sg (Z_to_bv 64 (z mod 2 ^ (8 * Z.of_nat (nbytes sz)))).
Proof.
intros E G sz sg rawv z HG Hraw.
destruct sz; cbn [loadres load_result nbytes nbits].
- rewrite s_ext2_sound, Hraw by exact HG. change (8 * Z.of_nat 1%nat) with (Z.of_N 8).
rewrite bv_extract0_mod by (cbn; lia). reflexivity.
- rewrite s_ext2_sound, Hraw by exact HG. change (8 * Z.of_nat 2%nat) with (Z.of_N 16).
rewrite bv_extract0_mod by (cbn; lia). reflexivity.
- rewrite s_ext2_sound, Hraw by exact HG. change (8 * Z.of_nat 4%nat) with (Z.of_N 32).
rewrite bv_extract0_mod by (cbn; lia). reflexivity.
- rewrite Hraw. change (8 * Z.of_nat 8%nat) with 64. symmetry. apply Z_to_bv64_mod.
Qed.
Lemma obase_eqb_eq : forall a b, obase_eqb a b = true -> a = b.
Proof.
intros [x|] [y|] H; cbn in H; try discriminate; [|reflexivity].
apply Nat.eqb_eq in H. congruence.
Qed.
Lemma find_region_sound : forall rs b off n r,
find_region rs b off n = Some r ->
In r rs /\ r_base r = b /\ r_lo r <= off /\ off + n <= r_hi r.
Proof.
induction rs as [|r0 rs IH]; cbn; intros b off n r H; [discriminate|].
destruct (obase_eqb (r_base r0) b && (r_lo r0 <=? off) && (off + n <=? r_hi r0)) eqn:Hc.
- injection H as <-. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply obase_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. auto.
- destruct (IH _ _ _ _ H) as (Hin & Hb & Hlo & Hhi). auto.
Qed.
Lemma find_chunk_sound : forall cs off n c,
find_chunk cs off n = Some c ->
In c cs /\ c_off c <= off /\ off + n <= c_off c + c_len c.
Proof.
induction cs as [|c0 cs IH]; cbn; intros off n c H; [discriminate|].
destruct ((c_off c0 <=? off) && (off + n <=? c_off c0 + c_len c0)) eqn:Hc.
- injection H as <-. apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. auto.
- destruct (IH _ _ _ H) as (Hin & Hlo & Hhi). auto.
Qed.
Lemma chunk_read : forall E m base c off n (f : nat -> byte),
chunk_ok E m base c ->
c_off c <= off -> off + Z.of_nat n <= c_off c + c_len c ->
(forall i, (i < n)%nat -> cbyte E (base + c_off c) (c_val c) (off - c_off c + Z.of_nat i) = Some (f i)) ->
rdn segs m (Z_to_bv 64 (base + off)) n = Some (map f (seq 0 n)).
Proof.
intros E m base c off n f Hc Hlo Hhi Hf.
apply rdn_mbytes. split; [rewrite length_map, length_seq; reflexivity|].
intros i Hi.
destruct (Hc (off - c_off c + Z.of_nat i) ltac:(lia)) as (b & Hb1 & Hb2).
rewrite Hf in Hb1 by exact Hi. injection Hb1 as <-.
replace (base + off + Z.of_nat i) with (base + c_off c + (off - c_off c + Z.of_nat i)) by lia.
rewrite Hb2. symmetry.
rewrite nth_error_map.
rewrite (nth_error_nth' (seq 0 n) 0%nat ltac:(rewrite length_seq; exact Hi)).
rewrite seq_nth by exact Hi. reflexivity.
Qed.
Lemma zbytes_as_map : forall z k n,
zbytes z k n = map (fun i => Z_to_bv 8 (Z.shiftr z (8 * (k + Z.of_nat i)))) (seq 0 n).
Proof.
intros z k n. revert k. induction n as [|n IH]; intros k; [reflexivity|].
cbn [zbytes seq map]. rewrite Z.add_0_r. f_equal.
rewrite IH. rewrite <- seq_shift, map_map. apply map_ext. intros i. f_equal. f_equal. lia.
Qed.
Lemma le_bytes_to_word_Z : forall bs, le_bytes_to_word bs = Z_to_bv 64 (bytes_le_to_Z bs).
Proof. reflexivity. Qed.
Lemma region_ok_chunk : forall E m r c,
region_ok E m r -> In c (r_chunks r) -> chunk_ok E m (base_val E (r_base r)) c.
Proof.
intros E m r c (_ & _ & _ & Hcs) Hin. rewrite Forall_forall in Hcs. apply Hcs. exact Hin.
Qed.
Lemma mem_ok_region : forall E m rs r, mem_ok E m rs -> In r rs -> region_ok E m r.
Proof.
intros E m rs r (_ & Hrs & _) Hin. rewrite Forall_forall in Hrs. apply Hrs. exact Hin.
Qed.
Lemma nbytes_pos : forall sz, (0 < nbytes sz)%nat /\ (nbytes sz <= 8)%nat.
Proof. destruct sz; cbn; lia. Qed.
Lemma srl_lit_small : forall E G v u k,
facts_ok E G ->
bv_unsigned (sv_denot E v) = u -> 0 <= k -> 8 * k < 64 ->
sv_denot E (s_alu G ALU_SRL v (SLit (8 * k))) = Z_to_bv 64 (Z.shiftr u (8 * k)).
Proof.
intros E G v u k HG Hu Hk Hk8. rewrite s_alu_sound by exact HG.
apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw sv_denot]. rewrite unsigned_lit, Hu.
rewrite (zcanon_small (8 * k)) by lia.
replace (Z.land (8 * k) 63) with (8 * k).
2:{ symmetry. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma img_bytes_spec : forall a n bs,
img_bytes a n = Some bs ->
length bs = n /\ forall i, (i < n)%nat -> img_byte (a + Z.of_nat i) = nth_error bs i.
Proof.
intros a n. revert a. induction n as [|n IH]; intros a bs H.
- cbn in H. injection H as <-. split; [reflexivity|]. intros; lia.
- cbn [img_bytes] in H. destruct (img_byte a) as [b|] eqn:Hb; [|discriminate].
destruct (img_bytes (a + 1) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
destruct (IH _ _ Hr) as [Hlen Hi]. split; [cbn; lia|].
intros i Hlt. destruct i as [|i]; cbn; [rewrite Z.add_0_r; exact Hb|].
rewrite <- Hi by lia. f_equal. lia.
Qed.
Lemma map_nth_seq : forall {A} (l : list A) (d : A) n, length l = n ->
map (fun i => nth i l d) (seq 0 n) = l.
Proof.
intros A l d n Hn. subst n. induction l as [|x l IH] using rev_ind; [reflexivity|].
rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, map_app. cbn [map].
rewrite Nat.add_0_l. rewrite nth_middle.
f_equal. rewrite <- IH at 2. apply map_ext_in. intros i Hi. apply in_seq in Hi.
rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma firstn_skipn_map : forall {A} n m (l : list A) (f : nat -> A),
(forall i, (i < n)%nat -> nth_error l (m + i)%nat = Some (f i)) ->
firstn n (skipn m l) = map f (seq 0 n).
Proof.
induction n as [|n IH]; intros m l f H; [reflexivity|].
cbn [seq map].
pose proof (H 0%nat ltac:(lia)) as H0. rewrite <- nth_error_skipn in H0.
destruct (skipn m l) as [|y r] eqn:Hs; [discriminate|].
cbn in H0. injection H0 as ->. cbn [firstn]. f_equal.
rewrite <- seq_shift, map_map.
replace r with (skipn (S m) l).
2:{ replace (S m) with (1 + m)%nat by lia. rewrite <- skipn_skipn, Hs. reflexivity. }
apply IH. intros i Hi. rewrite <- (H (S i)) by lia. f_equal. lia.
Qed.
Theorem sload_sound : forall E G m rs b off sz sg v,
facts_ok E G -> mem_ok E m rs ->
sload G rs b off sz sg = Some v ->
exists bs, rdn segs m (Z_to_bv 64 (base_val E b + off)) (nbytes sz) = Some bs /\
sv_denot E v = load_result sz sg (le_bytes_to_word bs).
Proof.
intros E G m rs b off sz sg v HG HM H. unfold sload in H.
destruct (find_region rs b off (Z.of_nat (nbytes sz))) as [r|] eqn:Hfr; [|discriminate].
apply find_region_sound in Hfr as (Hrin & Hrb & Hrlo & Hrhi).
destruct (find_chunk (r_chunks r) off (Z.of_nat (nbytes sz))) as [c|] eqn:Hfc; [|discriminate].
apply find_chunk_sound in Hfc as (Hcin & Hclo & Hchi).
pose proof (mem_ok_region E m rs r HM Hrin) as Hr.
pose proof (region_ok_chunk E m r c Hr Hcin) as Hc. rewrite Hrb in Hc.
pose proof (nbytes_pos sz) as Hn.
set (k := off - c_off c) in *.
destruct (c_val c) as [w cv | len | len | d s0 len] eqn:Hcv.
-
destruct (Z.of_N w <=? 8) eqn:Hw8; cbn [negb] in H; [|discriminate]. apply Z.leb_le in Hw8.
set (u := bv_unsigned (sv_denot E cv)).
exists (zbytes u k (nbytes sz)). split.
+ rewrite zbytes_as_map. eapply chunk_read; [exact Hc | lia | lia |].
intros i Hi. rewrite Hcv. cbn [cbyte]. unfold byte_of_word. f_equal.
+ rewrite le_bytes_to_word_Z, zbytes_spec by (subst u k; pose proof (u64_range (sv_denot E cv)); lia).
destruct (k =? 0) eqn:Hk0.
* injection H as <-. apply Z.eqb_eq in Hk0. rewrite Hk0, Z.mul_0_r, Z.shiftr_0_r.
apply (loadres_sound E G sz sg cv u HG). subst u. symmetry. apply lit_of_word.
* injection H as <-. apply Z.eqb_neq in Hk0.
assert (Hkw : k + Z.of_nat (nbytes sz) <= Z.of_N w).
{ subst k. unfold c_len in Hchi. rewrite Hcv in Hchi. cbn [cv_len] in Hchi. lia. }
apply (loadres_sound E G sz sg _ _ HG). apply (srl_lit_small E G cv u k HG eq_refl); lia.
-
injection H as <-. exists (repeat (Z_to_bv 8 0) (nbytes sz)). split.
+ replace (repeat (Z_to_bv 8 0) (nbytes sz)) with (map (fun _ : nat => Z_to_bv 8 0) (seq 0 (nbytes sz)))
by (rewrite map_const, length_seq; reflexivity).
eapply chunk_read; [exact Hc | lia | lia |]. intros i Hi. rewrite Hcv. reflexivity.
+ destruct sz, sg; vm_compute; reflexivity.
-
destruct b as [bn|]; [discriminate|].
destruct (img_bytes off (nbytes sz)) as [ibs|] eqn:Hib; [|discriminate]. injection H as <-.
apply img_bytes_spec in Hib as [Hlen Hib].
exists ibs. split.
+ rewrite <- (map_nth_seq ibs (Z_to_bv 8 0) (nbytes sz) Hlen).
eapply chunk_read; [exact Hc | lia | lia |]. intros i Hi. rewrite Hcv. cbn [cbyte base_val].
replace (0 + c_off c + (off - c_off c + Z.of_nat i)) with (off + Z.of_nat i) by lia.
rewrite Hib by exact Hi. apply nth_error_nth'. lia.
+ rewrite le_bytes_to_word_Z.
pose proof (loadres_sound E G sz sg (SLit (bytes_le_to_Z ibs)) (bytes_le_to_Z ibs) HG eq_refl) as HL.
rewrite HL. f_equal. f_equal. apply Z.mod_small.
pose proof (bytes_le_to_Z_nonneg ibs). pose proof (bytes_le_to_Z_bound ibs) as Hb.
rewrite Hlen in Hb. lia.
-
destruct (0 <=? s0) eqn:Hs0; [|discriminate]. apply Z.leb_le in Hs0.
injection H as <-.
assert (Hsk : 0 <= s0 + k) by (subst k; lia).
set (f := fun i : nat => match nth_error (ed E d) (Z.to_nat (s0 + k) + i)%nat with
| Some b0 => b0 | None => Z_to_bv 8 0 end).
assert (Hf : forall i, (i < nbytes sz)%nat -> nth_error (ed E d) (Z.to_nat (s0 + k) + i)%nat = Some (f i)).
{ intros i Hi. destruct (Hc (k + Z.of_nat i) ltac:(subst k; lia)) as (b0 & Hb1 & Hb2).
rewrite Hcv in Hb1. cbn [cbyte] in Hb1.
replace (Z.to_nat (s0 + (k + Z.of_nat i))) with (Z.to_nat (s0 + k) + i)%nat in Hb1 by lia.
unfold f. rewrite Hb1. reflexivity. }
exists (map f (seq 0 (nbytes sz))). split.
+ eapply chunk_read; [exact Hc | lia | lia |]. intros i Hi. rewrite Hcv. cbn [cbyte].
rewrite <- Hf by exact Hi. f_equal. subst k. lia.
+ pose proof (loadres_sound E G sz sg (SData d (s0 + k) (N.of_nat (nbytes sz)))
(data_word E d (s0 + k) (N.of_nat (nbytes sz))) HG eq_refl) as HL.
rewrite HL, le_bytes_to_word_Z. f_equal. f_equal.
unfold data_word. rewrite Nat2N.id.
rewrite (firstn_skipn_map (nbytes sz) (Z.to_nat (s0 + k)) (ed E d) f Hf).
apply Z.mod_small.
pose proof (bytes_le_to_Z_nonneg (map f (seq 0 (nbytes sz)))).
pose proof (bytes_le_to_Z_bound (map f (seq 0 (nbytes sz)))) as Hb.
rewrite length_map, length_seq in Hb. lia.
Qed.
Lemma writable_at_grows : forall m m' a, mem_grows m m' -> writable_at m a -> writable_at m' a.
Proof. intros m m' a Hg Hw. unfold writable_at in *. eapply wview_grows; eauto. Qed.
Lemma chunk_ok_wbytes_out : forall E m base c a bs,
0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
0 <= base + c_off c -> base + c_off c + c_len c <= 2^64 ->
(base + c_off c + c_len c <= a \/ a + Z.of_nat (length bs) <= base + c_off c) ->
chunk_ok E m base c -> chunk_ok E (wbytes m (Z_to_bv 64 a) bs) base c.
Proof.
intros E m base c a bs Ha Hnw Hlo Hhi Hdisj Hc i Hi.
destruct (Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
rewrite wbytes_mbyte; [|lia|lia|lia].
replace ((a <=? base + c_off c + i) && (base + c_off c + i <? a + Z.of_nat (length bs))) with false;
[exact Hb2|].
symmetry. apply andb_false_iff.
destruct Hdisj as [Hd|Hd]; [left; rewrite Z.leb_gt; lia | right; rewrite Z.ltb_ge; lia].
Qed.
Lemma cut_chunks_sound : forall E m base cs off n a bs,
a = base + off -> Z.of_nat (length bs) = n ->
0 <= a -> a + n <= 2^64 ->
(forall c, In c cs -> 0 <= base + c_off c /\ base + c_off c + c_len c <= 2^64 /\ 0 <= c_len c) ->
Forall (chunk_ok E m base) cs ->
Forall (chunk_ok E (wbytes m (Z_to_bv 64 a) bs) base) (cut_chunks cs off n).
Proof.
intros E m base cs off n a bs Ha Hlen Ha0 Hnw Hb Hcs.
induction cs as [|c cs IH]; [constructor|].
inversion Hcs as [|c' cs' Hc Hcs']; subst c' cs'.
assert (Hb' : forall c0, In c0 cs -> 0 <= base + c_off c0 /\ base + c_off c0 + c_len c0 <= 2^64 /\ 0 <= c_len c0)
by (intros c0 Hin; apply Hb; right; exact Hin).
specialize (IH Hb' Hcs').
destruct (Hb c (or_introl eq_refl)) as (Hc0 & Hc1 & Hc2).
cbn [cut_chunks].
destruct ((c_off c + c_len c <=? off) || (off + n <=? c_off c)) eqn:Hd.
- constructor; [|exact IH].
apply chunk_ok_wbytes_out; [lia|lia|lia|lia| |exact Hc].
apply orb_prop in Hd; destruct Hd as [Hd|Hd]; apply Z.leb_le in Hd; [left|right]; lia.
- apply Forall_app. split; [|apply Forall_app; split; [|exact IH]].
+ destruct (c_off c <? off) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl.
destruct (c_val c) as [w cv|len|len|d s0 len] eqn:Hcv; [constructor| | |].
all: apply orb_false_iff in Hd; destruct Hd as [Hd1 Hd2]; apply Z.leb_gt in Hd1; apply Z.leb_gt in Hd2.
all: unfold c_len in Hc1, Hc2, Hd1; rewrite Hcv in Hc1, Hc2, Hd1; cbn [cv_len c_val] in Hc1, Hc2, Hd1.
all: constructor; [intros i Hi; cbn [c_off c_val c_len cv_len] in Hi |- * | constructor].
all: destruct (Hc i ltac:(unfold c_len; rewrite Hcv; cbn; lia)) as (b0 & Hb1 & Hb2);
exists b0; rewrite Hcv in Hb1; cbn [cbyte] in Hb1 |- *; (split; [exact Hb1|]);
(rewrite wbytes_mbyte; [|lia|lia|lia]);
(replace ((a <=? base + c_off c + i) && (base + c_off c + i <? a + Z.of_nat (length bs))) with false;
[exact Hb2| symmetry; apply andb_false_iff; left; rewrite Z.leb_gt; lia]).
+ destruct (off + n <? c_off c + c_len c) eqn:Hr; [|constructor]. apply Z.ltb_lt in Hr.
apply orb_false_iff in Hd; destruct Hd as [Hd1 Hd2]; apply Z.leb_gt in Hd1; apply Z.leb_gt in Hd2.
destruct (c_val c) as [w cv|len|len|d s0 len] eqn:Hcv; [constructor| | |].
all: unfold c_len in Hc1, Hc2, Hd1, Hr |- *; rewrite Hcv in Hc1, Hc2, Hd1, Hr |- *;
cbn [cv_len c_val] in Hc1, Hc2, Hd1, Hr |- *.
all: constructor; [intros i Hi; cbn [c_off c_val c_len cv_len] in Hi |- * | constructor].
all: destruct (Hc (off + n - c_off c + i) ltac:(unfold c_len; rewrite Hcv; cbn; lia)) as (b0 & Hb1 & Hb2);
exists b0; rewrite Hcv in Hb1; cbn [cbyte] in Hb1 |- *;
(replace (base + (off + n) + i) with (base + c_off c + (off + n - c_off c + i)) by lia);
(split; [first [exact Hb1 | rewrite <- Hb1; f_equal; lia | rewrite <- Hb1; f_equal; f_equal; lia] |]);
(rewrite wbytes_mbyte; [|lia|lia|lia]);
(replace ((a <=? base + c_off c + (off + n - c_off c + i)) &&
(base + c_off c + (off + n - c_off c + i) <? a + Z.of_nat (length bs))) with false;
[exact Hb2| symmetry; apply andb_false_iff; right; rewrite Z.ltb_ge; lia]).
Qed.
Definition upd_region (r : region) (off n : Z) (cv : cval) : region :=
mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r)
(mkChunk off cv :: cut_chunks (r_chunks r) off n).
Lemma store_region_shape : forall rs b off n v rs',
store_region rs b off n v = Some rs' ->
exists l1 r l2, rs = l1 ++ r :: l2 /\ rs' = l1 ++ upd_region r off n v :: l2
/\ r_base r = b /\ r_lo r <= off /\ off + n <= r_hi r /\ r_wlo r <= off /\ off + n <= r_whi r.
Proof.
induction rs as [|r0 rs IH]; cbn; intros b off n v rs' H; [discriminate|].
destruct (obase_eqb (r_base r0) b && (r_lo r0 <=? off) && (off + n <=? r_hi r0)) eqn:Hc.
- destruct ((r_wlo r0 <=? off) && (off + n <=? r_whi r0)) eqn:Hw; [|discriminate].
injection H as <-.
apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply andb_prop in Hw as [H4 H5].
apply obase_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
apply Z.leb_le in H4. apply Z.leb_le in H5.
exists [], r0, rs. repeat split; auto.
- destruct (store_region rs b off n v) as [rs''|] eqn:Hs; [|discriminate]. injection H as <-.
destruct (IH _ _ _ _ _ Hs) as (l1 & r & l2 & -> & -> & Hb & H2 & H3 & H4 & H5).
exists (r0 :: l1), r, l2. repeat split; auto.
Qed.
Lemma pairwise_disjoint_split : forall E l1 r l2,
pairwise_disjoint E (l1 ++ r :: l2) ->
Forall (fun r' => extent_disjoint E r r') (l1 ++ l2).
Proof.
intros E l1 r l2. induction l1 as [|r0 l1 IH]; cbn; intros H.
- destruct H as [Hall _]. clear -Hall. induction l2 as [|r1 l2 IH2]; cbn in *; constructor; tauto.
- destruct H as [Hall Hpw]. constructor; [|apply IH; exact Hpw].
clear -Hall. induction l1 as [|r1 l1 IH1]; cbn in *.
+ destruct Hall as [Hd _]. unfold extent_disjoint in *. lia.
+ apply IH1. tauto.
Qed.
Definition extent_of (r : region) := (r_base r, r_lo r, r_hi r).
Lemma all_disjoint_extents : forall E r r' rs rs',
extent_of r = extent_of r' -> map extent_of rs = map extent_of rs' ->
all_disjoint E r rs -> all_disjoint E r' rs'.
Proof.
intros E r r' rs. revert r r'. induction rs as [|x rs IH]; intros r r' rs' Hr Hm H;
destruct rs' as [|y rs']; cbn in Hm; try discriminate; [exact I|].
assert (Hxy : extent_of x = extent_of y) by congruence.
assert (Hm' : map extent_of rs = map extent_of rs') by congruence.
cbn in H |- *. destruct H as [Hd Ha]. split.
- destruct r, r', x, y. unfold extent_of in Hr, Hxy. cbn in Hr, Hxy.
injection Hr as -> -> ->. injection Hxy as -> -> ->. exact Hd.
- eapply IH; eauto.
Qed.
Lemma pairwise_disjoint_extents : forall E rs rs',
map extent_of rs = map extent_of rs' -> pairwise_disjoint E rs -> pairwise_disjoint E rs'.
Proof.
intros E rs. induction rs as [|r rs IH]; intros rs' Hm H; destruct rs' as [|r' rs'];
cbn in Hm; try discriminate; [exact I|].
assert (Hr : extent_of r = extent_of r') by congruence.
assert (Hm' : map extent_of rs = map extent_of rs') by congruence.
cbn in H |- *. destruct H as [Ha Hp]. split.
- eapply all_disjoint_extents; eauto.
- apply IH; auto.
Qed.
Lemma map_extent_upd : forall l1 r l2 off n v,
map extent_of (l1 ++ upd_region r off n v :: l2) = map extent_of (l1 ++ r :: l2).
Proof. intros. rewrite !map_app. cbn. reflexivity. Qed.
Lemma regions_wf_app : forall l1 l2, regions_wf (l1 ++ l2) = regions_wf l1 && regions_wf l2.
Proof. induction l1 as [|r l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma cut_chunks_inside : forall r cs off n,
forallb (chunk_inside r) cs = true -> forallb (chunk_inside r) (cut_chunks cs off n) = true.
Proof.
intros r cs off n. induction cs as [|c cs IH]; cbn; intros H; [reflexivity|].
apply andb_prop in H as [Hc Hcs]. specialize (IH Hcs).
unfold chunk_inside in Hc. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct ((c_off c + c_len c <=? off) || (off + n <=? c_off c)) eqn:Hd.
- cbn. rewrite IH. unfold chunk_inside.
replace (r_lo r <=? c_off c) with true by (symmetry; apply Z.leb_le; lia).
replace (c_off c + c_len c <=? r_hi r) with true by (symmetry; apply Z.leb_le; lia).
replace (0 <=? c_len c) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- apply orb_false_iff in Hd as [Hd1 Hd2]. apply Z.leb_gt in Hd1. apply Z.leb_gt in Hd2.
rewrite !forallb_app, IH.
assert (HL : forallb (chunk_inside r)
(if c_off c <? off
then match c_val c with
| CVal _ _ => []
| CZero _ => [ {| c_off := c_off c; c_val := CZero (off - c_off c) |} ]
| CImg _ => [ {| c_off := c_off c; c_val := CImg (off - c_off c) |} ]
| CData d s _ => [ {| c_off := c_off c; c_val := CData d s (off - c_off c) |} ]
end
else []) = true).
{ destruct (c_off c <? off) eqn:Hl; [|reflexivity]. apply Z.ltb_lt in Hl.
destruct (c_val c); cbn; try reflexivity; unfold chunk_inside; cbn [c_off c_len cv_len c_val];
rewrite !andb_true_iff, !Z.leb_le; lia. }
assert (HR : forallb (chunk_inside r)
(if off + n <? c_off c + c_len c
then match c_val c with
| CVal _ _ => []
| CZero _ => [ {| c_off := off + n; c_val := CZero (c_off c + c_len c - (off + n)) |} ]
| CImg _ => [ {| c_off := off + n; c_val := CImg (c_off c + c_len c - (off + n)) |} ]
| CData d s _ => [ {| c_off := off + n; c_val := CData d (s + (off + n - c_off c)) (c_off c + c_len c - (off + n)) |} ]
end
else []) = true).
{ destruct (off + n <? c_off c + c_len c) eqn:Hl; [|reflexivity]. apply Z.ltb_lt in Hl.
destruct (c_val c); cbn; try reflexivity; unfold chunk_inside; cbn [c_off c_len cv_len c_val];
rewrite !andb_true_iff, !Z.leb_le; lia. }
rewrite HL, HR. reflexivity.
Qed.
Lemma region_wf_facts : forall r,
region_wf r = true ->
r_lo r <= r_hi r /\ (r_whi r <= r_wlo r \/ (r_lo r <= r_wlo r /\ r_whi r <= r_hi r))
/\ forallb (chunk_inside r) (r_chunks r) = true.
Proof.
intros r H. unfold region_wf in H.
apply andb_prop in H as [H Hc]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. split; [exact H1|]. split; [|exact Hc].
apply orb_prop in H2. destruct H2 as [H2|H2].
- left. apply Z.leb_le in H2. exact H2.
- right. apply andb_prop in H2 as [H2 H3]. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.
Lemma chunk_inside_facts : forall r c,
chunk_inside r c = true -> r_lo r <= c_off c /\ c_off c + c_len c <= r_hi r /\ 0 <= c_len c.
Proof.
intros r c H. unfold chunk_inside in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.
Lemma regions_wf_In : forall rs r, regions_wf rs = true -> In r rs -> region_wf r = true.
Proof.
induction rs as [|r0 rs IH]; cbn; intros r H Hin; [contradiction|].
apply andb_prop in H as [H0 H]. destruct Hin as [<-|Hin]; auto.
Qed.
Lemma new_chunk_ok : forall E m base off cv bs,
0 <= base + off -> base + off + Z.of_nat (length bs) <= 2^64 ->
cv_len cv = Z.of_nat (length bs) ->
(forall i, 0 <= i < Z.of_nat (length bs) -> cbyte E (base + off) cv i = nth_error bs (Z.to_nat i)) ->
chunk_ok E (wbytes m (Z_to_bv 64 (base + off)) bs) base (mkChunk off cv).
Proof.
intros E m base off cv bs Hlo Hhi Hlen Hcb i Hi. unfold c_len in Hi. cbn [c_off c_val] in Hi |- *.
rewrite Hlen in Hi.
destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hb.
2:{ exfalso. apply nth_error_None in Hb. lia. }
exists b. split; [rewrite Hcb by lia; exact Hb|].
rewrite wbytes_mbyte; [|lia|lia|lia].
replace ((base + off <=? base + off + i) && (base + off + i <? base + off + Z.of_nat (length bs))) with true
by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
replace (Z.to_nat (base + off + i - (base + off))) with (Z.to_nat i) by lia. exact Hb.
Qed.
Lemma st_bytes_cbyte : forall E base off n v i,
0 <= i < Z.of_nat n ->
cbyte E (base + off) (CVal (N.of_nat n) v) i = nth_error (st_bytes n (sv_denot E v)) (Z.to_nat i).
Proof.
intros E base off n v i Hi. cbn [cbyte]. unfold st_bytes, byte_of_word.
rewrite nth_error_zbytes by lia. f_equal. f_equal. f_equal. lia.
Qed.
Theorem swrite_sound : forall E m rs b off cv bs rs',
mem_ok E m rs ->
store_region rs b off (Z.of_nat (length bs)) cv = Some rs' ->
(0 < length bs)%nat -> cv_len cv = Z.of_nat (length bs) ->
(forall i, 0 <= i < Z.of_nat (length bs) -> cbyte E (base_val E b + off) cv i = nth_error bs (Z.to_nat i)) ->
store_ok segs m (Z_to_bv 64 (base_val E b + off)) (length bs) = true /\
mem_ok E (wbytes m (Z_to_bv 64 (base_val E b + off)) bs) rs'.
Proof.
intros E m rs b off cv bs rs' (Hwf & Hok & Hpd) H Hn Hcvl Hcb.
apply store_region_shape in H as (l1 & r & l2 & -> & -> & Hrb & Hlo & Hhi & Hwlo & Hwhi).
set (n := length bs) in *.
assert (Hrin : In r (l1 ++ r :: l2)) by (apply in_app_iff; right; left; reflexivity).
pose proof (regions_wf_In _ _ Hwf Hrin) as Hrwf.
apply region_wf_facts in Hrwf as (Hlohi & Hw & Hcin).
assert (Hwr : r_lo r <= r_wlo r /\ r_whi r <= r_hi r) by lia. clear Hw.
assert (Hr : region_ok E m r) by (rewrite Forall_forall in Hok; apply Hok; exact Hrin).
pose proof (pairwise_disjoint_split E l1 r l2 Hpd) as Hdis.
destruct Hr as (Hb0 & Hb1 & Hwrt & Hcs). rewrite Hrb in *.
split.
-
apply store_ok_of_all.
+ rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). lia.
+ intros x Hx. rewrite Z_to_bv_unsigned, bv_wrap_small in Hx by (change (bv_modulus 64) with (2^64); lia).
rewrite <- (lit_of_word x).
replace (bv_unsigned x) with (base_val E b + (bv_unsigned x - base_val E b)) by lia.
apply (Hwrt (bv_unsigned x - base_val E b)). lia.
- set (m' := wbytes m (Z_to_bv 64 (base_val E b + off)) bs).
assert (Hgrow : mem_grows m m') by (subst m'; apply wbytes_grows).
assert (Hlen : length bs = n) by reflexivity.
split; [|split].
+
rewrite regions_wf_app in Hwf |- *. cbn [regions_wf] in Hwf |- *.
apply andb_prop in Hwf as [Hwf1 Hwf2]. apply andb_prop in Hwf2 as [Hwfr Hwf2].
rewrite Hwf1, Hwf2, andb_true_r. cbn [andb].
unfold region_wf, upd_region in Hwfr |- *;
cbn [r_lo r_hi r_wlo r_whi r_chunks forallb] in Hwfr |- *.
apply andb_prop in Hwfr as [Hwfr Hcins]. rewrite Hwfr. cbn [andb].
apply andb_true_intro. split.
* unfold chunk_inside, c_len. cbn [c_off c_val r_lo r_hi]. rewrite Hcvl.
rewrite !andb_true_iff, !Z.leb_le. lia.
* apply cut_chunks_inside. exact Hcins.
+
assert (Hother : forall r', In r' (l1 ++ l2) -> region_ok E m r' -> region_ok E m' r').
{ intros r' Hin' (Hc0 & Hc1 & Hw' & Hcs').
rewrite Forall_forall in Hdis. specialize (Hdis r' Hin').
assert (Hwf' : region_wf r' = true).
{ apply (regions_wf_In (l1 ++ r :: l2)); [exact Hwf|].
apply in_app_iff in Hin'. apply in_app_iff.
destruct Hin'; [left; assumption| right; right; assumption]. }
apply region_wf_facts in Hwf' as (Hlohi' & _ & Hcin').
split; [exact Hc0|]. split; [exact Hc1|]. split.
- intros o Ho. eapply writable_at_grows; [exact Hgrow|]. apply Hw'. exact Ho.
- rewrite Forall_forall in Hcs' |- *. intros c Hc.
pose proof (proj1 (forallb_forall _ _) Hcin' c Hc) as Hci. apply chunk_inside_facts in Hci.
subst m'. apply chunk_ok_wbytes_out; try (rewrite ?Hlen; lia).
+ rewrite Hlen. unfold extent_disjoint in Hdis. rewrite Hrb in Hdis.
destruct Hdis; [right|left]; lia.
+ apply Hcs'. exact Hc. }
assert (Hokl : Forall (region_ok E m) (l1 ++ l2)).
{ rewrite Forall_forall in Hok |- *. intros r' Hin'. apply Hok.
apply in_app_iff in Hin'. apply in_app_iff.
destruct Hin'; [left; assumption| right; right; assumption]. }
apply Forall_app in Hokl as [Hokl1 Hokl2].
apply Forall_app. split; [|constructor].
* rewrite Forall_forall in Hokl1 |- *. intros r' Hin'.
apply Hother; [apply in_app_iff; left; exact Hin'|]. apply Hokl1. exact Hin'.
*
unfold upd_region, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]. rewrite Hrb.
split; [exact Hb0|]. split; [exact Hb1|]. split.
-- intros o Ho. eapply writable_at_grows; [exact Hgrow|]. apply Hwrt. exact Ho.
-- constructor.
++ subst m'. apply new_chunk_ok; [lia|lia|exact Hcvl|exact Hcb].
++ subst m'. eapply cut_chunks_sound;
[reflexivity| rewrite Hlen; reflexivity | lia | lia | | exact Hcs].
intros c Hc. pose proof (proj1 (forallb_forall _ _) Hcin c Hc) as Hci.
apply chunk_inside_facts in Hci. lia.
* rewrite Forall_forall in Hokl2 |- *. intros r' Hin'.
apply Hother; [apply in_app_iff; right; exact Hin'|]. apply Hokl2. exact Hin'.
+ eapply pairwise_disjoint_extents; [|exact Hpd]. symmetry. apply map_extent_upd.
Qed.
Theorem sstore_sound : forall E m rs b off sz v rs',
mem_ok E m rs ->
sstore rs b off sz v = Some rs' ->
store_ok segs m (Z_to_bv 64 (base_val E b + off)) (nbytes sz) = true /\
mem_ok E (wbytes m (Z_to_bv 64 (base_val E b + off)) (st_bytes (nbytes sz) (sv_denot E v))) rs'.
Proof.
intros E m rs b off sz v rs' HM H. unfold sstore in H.
pose proof (length_zbytes (bv_unsigned (sv_denot E v)) 0 (nbytes sz)) as Hlen.
fold (st_bytes (nbytes sz) (sv_denot E v)) in Hlen.
rewrite <- Hlen in H at 1. rewrite <- Hlen at 1.
eapply swrite_sound; [exact HM | exact H | rewrite Hlen; pose proof (nbytes_pos sz); lia
| cbn; rewrite Hlen; lia |].
intros i Hi. rewrite Hlen in Hi. apply st_bytes_cbyte. exact Hi.
Qed.
Definition skel (r : region) := (r_base r, r_lo r, r_hi r, r_wlo r, r_whi r).
Definition skeleton (rs : smem) := map skel rs.
Definition in_wrange (E : env) (rs : smem) (a : Z) : Prop :=
exists r, In r rs /\ base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r.
Definition frame_of (E : env) (rs : smem) (m m' : word -> option byte) : Prop :=
forall x : word, ~ in_wrange E rs (bv_unsigned x) -> m' x = m x.
Lemma frame_of_refl : forall E rs m, frame_of E rs m m.
Proof. intros E rs m x _. reflexivity. Qed.
Lemma in_wrange_skeleton : forall E rs rs' a,
skeleton rs = skeleton rs' -> in_wrange E rs a -> in_wrange E rs' a.
Proof.
intros E rs. induction rs as [|r rs IH]; intros rs' a Hsk (r0 & Hin & Hr0);
destruct rs' as [|r' rs']; try (cbn in Hsk; discriminate); [destruct Hin|].
pose proof (f_equal (@hd _ (skel r)) Hsk) as Hrr. pose proof (f_equal (@tl _) Hsk) as Hsk'.
cbn [hd tl skeleton map] in Hrr, Hsk'. change (map skel rs = map skel rs') in Hsk'.
destruct Hin as [<-|Hin].
- exists r'. split; [left; reflexivity|].
destruct r, r'. unfold skel in Hrr. cbn in Hrr, Hr0 |- *.
inversion Hrr. subst. exact Hr0.
- destruct (IH rs' a Hsk' (ex_intro _ r0 (conj Hin Hr0))) as (r1 & Hin1 & Hr1).
exists r1. split; [right; exact Hin1| exact Hr1].
Qed.
Lemma frame_of_trans : forall E rs rs' m1 m2 m3,
skeleton rs = skeleton rs' ->
frame_of E rs m1 m2 -> frame_of E rs' m2 m3 -> frame_of E rs m1 m3.
Proof.
intros E rs rs' m1 m2 m3 Hsk H12 H23 x Hx.
rewrite H23; [apply H12; exact Hx|].
intros Hin. apply Hx. eapply in_wrange_skeleton; [symmetry; exact Hsk| exact Hin].
Qed.
Lemma store_region_skeleton : forall rs b off n cv rs',
store_region rs b off n cv = Some rs' -> skeleton rs' = skeleton rs.
Proof.
intros rs b off n cv rs' H.
apply store_region_shape in H as (l1 & r & l2 & -> & -> & _).
unfold skeleton. rewrite !map_app. cbn. reflexivity.
Qed.
Lemma store_region_frame : forall E m rs b off cv bs rs',
mem_ok E m rs ->
store_region rs b off (Z.of_nat (length bs)) cv = Some rs' -> (0 < length bs)%nat ->
frame_of E rs m (wbytes m (Z_to_bv 64 (base_val E b + off)) bs).
Proof.
intros E m rs b off cv bs rs' (Hwf & Hok & Hpd) H Hn x Hx.
apply store_region_shape in H as (l1 & r & l2 & -> & -> & Hrb & Hlo & Hhi & Hwlo & Hwhi).
subst b.
assert (Hrin : In r (l1 ++ r :: l2)) by (apply in_app_iff; right; left; reflexivity).
assert (Hr : region_ok E m r) by (rewrite Forall_forall in Hok; apply Hok; exact Hrin).
destruct Hr as (Hb0 & Hb1 & _).
pose proof (regions_wf_In _ _ Hwf Hrin) as Hrwf. apply region_wf_facts in Hrwf as (Hlohi & Hw & _).
pose proof (u64_range x) as Hxr.
set (a := base_val E (r_base r) + off) in *.
assert (HB : 0 <= a /\ a + Z.of_nat (length bs) <= 2^64) by (subst a; lia).
assert (Hua : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
destruct (Z_lt_le_dec (bv_unsigned x) a).
- apply wbytes_below; rewrite Hua; lia.
- destruct (Z_lt_le_dec (bv_unsigned x) (a + Z.of_nat (length bs))).
+ exfalso. apply Hx. exists r. split; [exact Hrin|]. subst a. lia.
+ apply wbytes_above. rewrite Hua. lia.
Qed.
End e.
