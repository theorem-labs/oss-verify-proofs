(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0g YO0a YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN0b YN07 YN0a
YN1z YN20 YN21 YN22.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Abbreviation B := src0_msyms.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sr_get_nat sr n : (1 <= n <= 31)%nat -> sr_get sr (nat_to_reg n) = nth n sr (SLit 0).
Proof. intros Hn. do 32 (destruct n as [|n]; [reflexivity || lia|]). lia. Qed.
Lemma reg_of E ss ms n e : st_ok src0segs E ss ms -> (1 <= n <= 31)%nat -> nth n (ss_regs ss) (SLit 0) = e ->
getr (ms_regs ms) (nat_to_reg n) = sv_denot E e.
Proof. intros HS Hn He. rewrite (st_ok_reg src0segs E ss ms (nat_to_reg n) HS), sr_get_nat, He by exact Hn. reflexivity. Qed.
Lemma regs_lit_nth l n : (n < 32)%nat ->
nth n (regs_lit l) (SLit 0) =
match find (fun p => Nat.eqb (fst p) n) l with
| Some (_, z) => SLit z
| None => if Nat.eqb n 0 then SLit 0 else SOff n 0
end.
Proof.
intros Hn. unfold regs_lit.
set (f := fun i : nat => match find (fun p : nat * Z => Nat.eqb (fst p) i) l with Some (_, z) => SLit z | None => if Nat.eqb i 0 then SLit 0 else SOff i 0 end).
change (nth n (map f (seq 0 32)) (SLit 0) = f n).
rewrite (nth_indep _ (SLit 0) (f 32%nat)) by (rewrite length_map, length_seq; exact Hn).
rewrite map_nth, seq_nth by exact Hn. reflexivity.
Qed.
Lemma regs_sv_nth l n : (n < 32)%nat ->
nth n (regs_sv l) (SLit 0) =
match find (fun p => Nat.eqb (fst p) n) l with
| Some (_, v) => v
| None => if Nat.eqb n 0 then SLit 0 else SOff n 0
end.
Proof.
intros Hn. unfold regs_sv.
set (f := fun i : nat => match find (fun p : nat * sv => Nat.eqb (fst p) i) l with Some (_, v) => v | None => if Nat.eqb i 0 then SLit 0 else SOff i 0 end).
change (nth n (map f (seq 0 32)) (SLit 0) = f n).
rewrite (nth_indep _ (SLit 0) (f 32%nat)) by (rewrite length_map, length_seq; exact Hn).
rewrite map_nth, seq_nth by exact Hn. reflexivity.
Qed.
Lemma regs_ok_lit xv l regs :
(forall n, (1 <= n <= 31)%nat ->
match find (fun p => Nat.eqb (fst p) n) l with
| Some (_, z) => getr regs (nat_to_reg n) = Z_to_bv 64 z
| None => getr regs (nat_to_reg n) = Z_to_bv 64 (xv n)
end) ->
regs_ok (EV xv) (regs_lit l) regs.
Proof.
intros H r. unfold sr_get. pose proof (u5_range r) as Hr. destruct (bv_eqb r 0) eqn:E.
- unfold getr. rewrite E. reflexivity.
- assert (Hr0 : bv_unsigned r <> 0).
{ intros Z0. assert (r = 0%bv) as -> by (apply bv_eq; exact Z0). rewrite bv_eqb_refl in E. discriminate. }
unfold ridx. rewrite regs_lit_nth by lia.
specialize (H (Z.to_nat (bv_unsigned r)) ltac:(lia)). rewrite nat_to_reg_ridx in H.
destruct (find _ l) as [[k z]|].
+ rewrite H. reflexivity.
+ replace (Nat.eqb (Z.to_nat (bv_unsigned r)) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
cbn [sv_denot EV ew]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H.
Qed.
Lemma regs_ok_sv xv l regs :
(forall n, (1 <= n <= 31)%nat ->
match find (fun p => Nat.eqb (fst p) n) l with
| Some (_, v) => getr regs (nat_to_reg n) = sv_denot (EV xv) v
| None => getr regs (nat_to_reg n) = Z_to_bv 64 (xv n)
end) ->
regs_ok (EV xv) (regs_sv l) regs.
Proof.
intros H r. unfold sr_get. pose proof (u5_range r) as Hr. destruct (bv_eqb r 0) eqn:E.
- unfold getr. rewrite E. reflexivity.
- assert (Hr0 : bv_unsigned r <> 0).
{ intros Z0. assert (r = 0%bv) as -> by (apply bv_eq; exact Z0). rewrite bv_eqb_refl in E. discriminate. }
unfold ridx. rewrite regs_sv_nth by lia.
specialize (H (Z.to_nat (bv_unsigned r)) ltac:(lia)). rewrite nat_to_reg_ridx in H.
destruct (find _ l) as [[k z]|].
+ rewrite H. reflexivity.
+ replace (Nat.eqb (Z.to_nat (bv_unsigned r)) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
cbn [sv_denot EV ew]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H.
Qed.
Lemma frame_of_nowin E rs m m' :
Forall (fun r => r_wlo r = 0 /\ r_whi r = 0) rs -> frame_of E rs m m' -> m' = m.
Proof.
intros Hrs HF. apply functional_extensionality. intros x. apply HF.
intros (r & Hin & Hr). pose proof (proj1 (Forall_forall _ _) Hrs r Hin) as [W1 W2]. rewrite W1, W2 in Hr. lia.
Qed.
Lemma cview_regs l ss pc rv mm svs :
cview l ss = (pc, rv, mm, svs) ->
ss_pc ss = pc /\ ss_resv ss = rv /\ ss_mem ss = mm /\
forall i, (i < length l)%nat -> nth (nth i l 0%nat) (ss_regs ss) (SLit 0) = nth i svs (SLit 0).
Proof.
intros V. unfold cview in V. injection V as V1 V2 V3 V4. repeat split; try assumption.
intros i Hi. rewrite <- V4.
set (f := fun n0 : nat => nth n0 (ss_regs ss) (SLit 0)).
transitivity (nth i (map f l) (f 0%nat)); [| apply nth_indep; rewrite length_map; exact Hi].
rewrite map_nth. reflexivity.
Qed.
End d.
Ltac reg_eq V i :=
let H := fresh in
pose proof (proj2 (proj2 (proj2 (cview_regs _ _ _ _ _ _ V))) i ltac:(cbn; lia)) as H;
cbn [nth app length CSAVED csaved_svs map T0_VIEW T1_VIEW T2_VIEW T2c_VIEW T4f_VIEW tl t0b_mem] in H; exact H.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FRAME_SLOTS : list (Z * nat) := [(0, 20%nat); (8, 19%nat); (16, 18%nat); (24, 9%nat); (32, 8%nat); (40, 1%nat)].
Lemma csaved_cases i : In i CSAVED -> i = 3%nat \/ i = 21%nat \/ i = 22%nat \/ i = 23%nat \/ i = 24%nat \/ i = 25%nat \/ i = 26%nat \/ i = 27%nat.
Proof. unfold CSAVED. cbn. intuition lia. Qed.
Lemma mbyte_ext m m' a : m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte src0segs m' a = mbyte src0segs m a.
Proof. intros E. unfold mbyte. rewrite E. reflexivity. Qed.
Lemma writable_ext m m' a : m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at src0segs m a <-> writable_at src0segs m' a).
Proof. intros E. unfold writable_at, wview. rewrite E. tauto. Qed.
Lemma present_writable m a : present m a -> writable_at src0segs m a.
Proof. intros [b Hb]. unfold writable_at, wview. rewrite Hb. discriminate. Qed.
Lemma bytes_are_ext m m' a w v : (forall i, 0 <= i < Z.of_nat w -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i))) ->
bytes_are m a w v -> bytes_are m' a w v.
Proof. intros E Hb k Hk. rewrite (mbyte_ext m m') by (apply E; lia). apply Hb. exact Hk. Qed.
Lemma shiftr_mod_byte v n k : 0 <= k -> 0 <= n -> k + 8 <= n ->
(Z.shiftr (v mod 2 ^ n) k) mod 2 ^ 8 = (Z.shiftr v k) mod 2 ^ 8.
Proof.
intros Hk Hn Hkn. rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
rewrite !Z.land_spec, !Z.shiftr_spec, !Z.land_spec, !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 8) eqn:E8; [|rewrite !Bool.andb_false_r; reflexivity]. apply Z.ltb_lt in E8.
replace (i + k <? n) with true by (symmetry; apply Z.ltb_lt; lia). rewrite !Bool.andb_true_r. reflexivity.
Qed.
Lemma chunk_bytes xv m base off (w : N) e v :
chunk_ok src0segs (EV xv) m base (mkChunk off (CVal w e)) -> bv_unsigned (sv_denot (EV xv) e) = v ->
bytes_are m (base + off) (N.to_nat w) (v mod 2 ^ (8 * Z.of_N w)).
Proof.
intros Hc Hv k Hk. destruct (Hc (Z.of_nat k) ltac:(cbn [c_len c_val cv_len]; lia)) as (b & Hb1 & Hb2).
cbn [c_off c_val cbyte] in Hb1, Hb2. rewrite Hb2. injection Hb1 as <-. f_equal.
unfold byte_of_word, le_byte. rewrite Hv, <- (Z_to_bv8_mod (Z.shiftr v _)). f_equal. rewrite N_nat_Z.
rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). change 256 with (2 ^ 8). symmetry. apply shiftr_mod_byte; lia.
Qed.
Lemma chunk_bytes_small xv m base off (w : N) e v :
chunk_ok src0segs (EV xv) m base (mkChunk off (CVal w e)) -> bv_unsigned (sv_denot (EV xv) e) = v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
bytes_are m (base + off) (N.to_nat w) v.
Proof. intros Hc Hv Hr. rewrite <- (Z.mod_small v (2 ^ (8 * Z.of_N w))) by lia. exact (chunk_bytes xv m base off w e v Hc Hv). Qed.
Fixpoint sv_uses (P : nat -> bool) (v : sv) : bool :=
match v with
| SLit _ => true
| SOff n _ => P n
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => sv_uses P a && sv_uses P b
| SExt _ _ a => sv_uses P a
| SData _ _ _ => false
| SF1 _ a => sv_uses P a
| SF2 _ a b => sv_uses P a && sv_uses P b
| SF3 _ a b c => sv_uses P a && sv_uses P b && sv_uses P c
end.
Lemma sv_denot_agree P E E' v :
sv_uses P v = true -> (forall n, P n = true -> ew E n = ew E' n) -> sv_denot E v = sv_denot E' v.
Proof.
intros Hv HE. induction v; cbn in *; try discriminate;
try (apply andb_prop in Hv as [Ha Hb]; rewrite (IHv1 Ha), (IHv2 Hb); reflexivity).
- reflexivity.
- rewrite (HE n Hv). reflexivity.
- rewrite (IHv Hv). reflexivity.
- rewrite (IHv Hv). reflexivity.
- apply andb_prop in Hv as [Hab Hc]. apply andb_prop in Hab as [Ha Hb].
rewrite (IHv1 Ha), (IHv2 Hb), (IHv3 Hc). reflexivity.
Qed.
Definition xv_of (l : list (nat * Z)) (i : nat) : Z :=
match find (fun p => Nat.eqb (fst p) i) l with Some (_, z) => z | None => 0 end.
Definition uses_of (l : list (nat * Z)) (i : nat) : bool := existsb (fun p => Nat.eqb (fst p) i) l.
Lemma xv_of_agree (l : list (nat * Z)) xv :
(forall p, In p l -> xv (fst p) = snd p) ->
forall n, uses_of l n = true -> ew (EV xv) n = ew (EV (xv_of l)) n.
Proof.
intros H n Hn. cbn [ew EV]. f_equal. unfold xv_of. unfold uses_of in Hn.
induction l as [|[a z] l IH]; cbn in *; [discriminate|].
destruct (Nat.eqb a n) eqn:E; cbn in Hn.
- apply Nat.eqb_eq in E. subst a. exact (H (n, z) (or_introl eq_refl)).
- apply IH; [| exact Hn]. intros p Hp. apply H. right. exact Hp.
Qed.
Definition Uof (l : list (nat * Z)) (v : sv) : Z := bv_unsigned (sv_denot (EV (xv_of l)) v).
Lemma U_by_atoms l xv v :
sv_uses (uses_of l) v = true -> (forall p, In p l -> xv (fst p) = snd p) ->
U (EV xv) v = Uof l v.
Proof. intros Hv H. unfold U, Uof. rewrite (sv_denot_agree _ (EV xv) (EV (xv_of l)) v Hv (xv_of_agree l xv H)). reflexivity. Qed.
Lemma denot_by_atoms l xv v :
sv_uses (uses_of l) v = true -> (forall p, In p l -> xv (fst p) = snd p) ->
sv_denot (EV xv) v = Z_to_bv 64 (Uof l v).
Proof. intros Hv H. rewrite (denot_lit_U (EV xv) v), (U_by_atoms l xv v Hv H). reflexivity. Qed.
Fixpoint UZ (xv : nat -> Z) (v : sv) : Z :=
match v with
| SLit z => zcanon z
| SOff n z => zcanon (zcanon (xv n) + z)
| SAlu op a b => zalu64 op (UZ xv a) (UZ xv b)
| SAluw op a b => zalu32 op (UZ xv a) (UZ xv b)
| SMd op a b => zmd64 op (UZ xv a) (UZ xv b)
| SMdw op a b => zmd32 op (UZ xv a) (UZ xv b)
| SExt sg w a => zext_low sg w (UZ xv a)
| SData _ _ _ => 0
| SF1 op a => bv_unsigned (fpop1_denot op (Z_to_bv 64 (UZ xv a)))
| SF2 op a b => bv_unsigned (fpop2_denot op (Z_to_bv 64 (UZ xv a)) (Z_to_bv 64 (UZ xv b)))
| SF3 op a b c => bv_unsigned (fpop3_denot op (Z_to_bv 64 (UZ xv a)) (Z_to_bv 64 (UZ xv b)) (Z_to_bv 64 (UZ xv c)))
end.
Lemma UZ_sound xv v : sv_denot (EV xv) v = Z_to_bv 64 (UZ xv v).
Proof.
induction v; cbn [sv_denot UZ].
- symmetry. apply Z_to_bv64_canon.
- cbn [ew EV]. rewrite unsigned_lit. symmetry. apply Z_to_bv64_canon.
- rewrite IHv1, IHv2. apply zalu64_sound.
- rewrite IHv1, IHv2. apply zalu32_sound.
- rewrite IHv1, IHv2. apply zmd64_sound.
- rewrite IHv1, IHv2. apply zmd32_sound.
- rewrite IHv. destruct sg; [exact (zext_low_sound true w (UZ xv v)) | exact (zext_low_sound false w (UZ xv v))].
- unfold data_word. cbn [ed EV]. rewrite skipn_nil, firstn_nil. reflexivity.
- rewrite IHv. symmetry. apply Z_to_bv_bv_unsigned.
- rewrite IHv1, IHv2. symmetry. apply Z_to_bv_bv_unsigned.
- rewrite IHv1, IHv2, IHv3. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma UZ_range xv v : 0 <= UZ xv v < 2 ^ 64.
Proof.
pose proof (u64_range (sv_denot (EV xv) v)) as H. rewrite UZ_sound, Z_to_bv_unsigned in H.
destruct v; cbn [UZ]; try apply zcanon_range; try apply u64_range. lia.
Qed.
Lemma U_UZ xv v : U (EV xv) v = UZ xv v.
Proof. unfold U. rewrite UZ_sound, Z_to_bv_unsigned. apply bv_wrap_small. pose proof (UZ_range xv v). change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Definition UZof (l : list (nat * Z)) (v : sv) : Z := UZ (xv_of l) v.
Lemma UZ_by_atoms l xv v :
sv_uses (uses_of l) v = true -> (forall p, In p l -> xv (fst p) = snd p) ->
sv_denot (EV xv) v = Z_to_bv 64 (UZof l v).
Proof. intros Hv H. rewrite (denot_by_atoms l xv v Hv H). unfold Uof, UZof. rewrite <- U_UZ. reflexivity. Qed.
Definition deb_chk (i : Z) : bool :=
match seg_rom src0segs (Z_to_bv 64 (DEB + i)) with
| Some b => Z.eqb (bv_unsigned b) (znth i DEBRUIJN)
| None => false
end.
Lemma deb_chk_all : forallb deb_chk (zseq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma deb_rom i : 0 <= i < 32 -> seg_rom src0segs (Z_to_bv 64 (DEB + i)) = Some (Z_to_bv 8 (znth i DEBRUIJN)).
Proof.
intros Hi. pose proof (proj1 (forallb_zseq_iff deb_chk 0 32) deb_chk_all i Hi) as C. unfold deb_chk in C.
destruct (seg_rom src0segs (Z_to_bv 64 (DEB + i))) as [b|]; [|discriminate]. apply Z.eqb_eq in C.
f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- C. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Definition sct_chk (i : Z) : bool :=
match seg_rom src0segs (Z_to_bv 64 (SCT + 2 * i)), seg_rom src0segs (Z_to_bv 64 (SCT + 2 * i + 1)) with
| Some b0, Some b1 => Z.eqb (bv_unsigned b0) (znth i size_classes mod 256) && Z.eqb (bv_unsigned b1) (znth i size_classes / 256)
| _, _ => false
end.
Lemma sct_chk_all : forallb sct_chk (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sct_rom i : 0 <= i < 48 ->
seg_rom src0segs (Z_to_bv 64 (SCT + 2 * i)) = Some (Z_to_bv 8 (znth i size_classes mod 256)) /\
seg_rom src0segs (Z_to_bv 64 (SCT + 2 * i + 1)) = Some (Z_to_bv 8 (znth i size_classes / 256)).
Proof.
intros Hi. pose proof (proj1 (forallb_zseq_iff sct_chk 0 48) sct_chk_all i Hi) as C. unfold sct_chk in C.
destruct (seg_rom src0segs (Z_to_bv 64 (SCT + 2 * i))) as [b0|]; [|discriminate].
destruct (seg_rom src0segs (Z_to_bv 64 (SCT + 2 * i + 1))) as [b1|]; [|discriminate].
apply andb_prop in C as [C0 C1]. apply Z.eqb_eq in C0. apply Z.eqb_eq in C1.
split; f_equal; apply bv_eq; rewrite Z_to_bv_unsigned; [rewrite <- C0 | rewrite <- C1]; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range.
Qed.
Lemma size_classes_range i : 0 <= i < 48 -> 1 <= znth i size_classes <= 8191.
Proof.
intros Hi.
assert (C : forallb (fun i => (1 <=? znth i size_classes) && (znth i size_classes <=? 8191)) (zseq 0 48) = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_zseq_iff _ 0 48) C i Hi) as Ci. apply andb_prop in Ci as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.
Section h.
Variable mem : word -> option byte.
Hypothesis ST : statics_ok B mem.
Lemma deb_byte i : 0 <= i < 32 -> bytes_are mem (DEB + i) 1 (znth i DEBRUIJN).
Proof.
intros Hi k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (st_tables _ _ ST) by (unfold table_addr; cbn [ms_debruijn src0_msyms]; unfold DEB; lia).
change (ms_segs B) with src0segs. unfold w64. rewrite (deb_rom i Hi). f_equal. f_equal. unfold le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
pose proof (proj1 (forallb_zseq_iff (fun i => (0 <=? znth i DEBRUIJN) && (znth i DEBRUIJN <? 32)) 0 32) ltac:(vm_compute; reflexivity) i Hi) as R.
apply andb_prop in R as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
rewrite (Z.mod_small _ (2 ^ 8)), Z.mod_small by lia. reflexivity.
Qed.
Lemma sct_bytes i : 0 <= i < 48 -> bytes_are mem (SCT + 2 * i) 2 (znth i size_classes).
Proof.
intros Hi k Hk. pose proof (size_classes_range i Hi) as R. destruct (sct_rom i Hi) as [S0 S1].
assert (TA : forall a, SCT <= a < SCT + 96 -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a)).
{ intros a Ha. rewrite (st_tables _ _ ST) by (unfold table_addr; cbn [ms_size_classes src0_msyms]; unfold SCT in Ha; lia). reflexivity. }
change (ms_segs B) with src0segs in TA.
destruct k as [|[|k]]; [| | lia]; cbn [Z.of_nat]; rewrite TA by lia.
- rewrite Z.add_0_r, S0. f_equal. f_equal. unfold le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r, (Z.mod_small _ (2 ^ 16)) by lia. reflexivity.
- change (Z.of_nat 1) with 1. rewrite S1. f_equal. f_equal. unfold le_byte. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 1) with 8.
rewrite (Z.mod_small _ (2 ^ 16)), Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.mod_small; [reflexivity|].
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
End h.
End g.
