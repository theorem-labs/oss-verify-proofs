(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP08.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Lemma nth_error_app_off : forall {A} (l1 l2 : list A) j,
nth_error (l1 ++ l2) (length l1 + j) = nth_error l2 j.
Proof. intros A l1 l2 j. rewrite nth_error_app2 by lia. f_equal. lia. Qed.
Lemma nth_error_flat_map_le8 : forall (l : list word) k i,
(k < length l)%nat -> (i < 8)%nat ->
nth_error (flat_map word_le8 l) (8 * k + i) = nth_error (word_le8 (nth k l (Z_to_bv 64 0))) i.
Proof.
induction l as [|w l IH]; intros k i Hk Hi; [cbn in Hk; lia|].
cbn [flat_map nth]. destruct k as [|k].
- rewrite nth_error_app1 by (rewrite length_n_to_le_8; lia). f_equal; lia.
- replace (8 * S k + i)%nat with (length (word_le8 w) + (8 * k + i))%nat
by (rewrite length_n_to_le_8; lia).
rewrite nth_error_app_off. apply IH; [cbn in Hk; lia| exact Hi].
Qed.
Lemma nth_error_flatten_strings : forall (l : list (list byte)) k j,
(k < length l)%nat -> (j <= length (nth k l []))%nat ->
nth_error (flatten_strings l) (total_arg_bytes_nat (firstn k l) + j)
= nth_error (nth k l [] ++ [Z_to_bv 8 0]) j.
Proof.
induction l as [|s l IH]; intros k j Hk Hj; [cbn in Hk; lia|].
cbn [flatten_strings flat_map nth firstn] in *. fold (flatten_strings l).
destruct k as [|k].
- change (total_arg_bytes_nat []) with 0%nat. rewrite Nat.add_0_l.
cbn [nth] in Hj. apply nth_error_app1. rewrite length_app. cbn [length]. lia.
- cbn [firstn]. rewrite total_arg_bytes_cons.
replace (length s + 1 + total_arg_bytes_nat (firstn k l) + j)%nat
with (length (s ++ [Z_to_bv 8 0]) + (total_arg_bytes_nat (firstn k l) + j))%nat
by (rewrite length_app; cbn [length]; lia).
rewrite nth_error_app_off. apply IH; [cbn in Hk; lia| exact Hj].
Qed.
Lemma word_le8_nth : forall (w : word) i, (i < 8)%nat ->
nth_error (word_le8 w) i = Some (byte_of_word w (Z.of_nat i)).
Proof.
intros w i Hi.
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try reflexivity. lia.
Qed.
Lemma word_le8_st_bytes : forall w : word, word_le8 w = st_bytes 8 w.
Proof. intros w. reflexivity. Qed.
Fixpoint auxv_words (l : list (word * word)) : list word :=
match l with [] => [] | (k, v) :: r => k :: v :: auxv_words r end.
Lemma build_auxv_words : forall l, build_auxv l = flat_map word_le8 (auxv_words l).
Proof.
induction l as [|[k v] l IH]; [reflexivity|].
cbn [build_auxv auxv_words flat_map fst snd]. fold (build_auxv l). rewrite IH, app_assoc. reflexivity.
Qed.
Lemma length_auxv_words : forall l, length (auxv_words l) = (2 * length l)%nat.
Proof. induction l as [|[k v] l IH]; [reflexivity|]. cbn [auxv_words length]. rewrite IH. lia. Qed.
Definition raw_len (av ev : list (list byte)) : nat :=
(8 + (length av + 1) * 8 + (length ev + 1) * 8 + auxv_size
+ length (flatten_strings av) + length (flatten_strings ev))%nat.
Definition pad_len (av ev : list (list byte)) : nat :=
Z.to_nat ((8 - Z.of_nat (raw_len av ev) mod 8) mod 8).
Definition rand_off (av ev : list (list byte)) : nat := (raw_len av ev + pad_len av ev)%nat.
Lemma at_random_ptr_eq : forall sp av ev,
at_random_ptr sp av ev = (sp + nat_to_word (rand_off av ev))%bv.
Proof. reflexivity. Qed.
Lemma raw_len_eq : forall av ev,
raw_len av ev = (cat_struct_size av ev + total_arg_bytes_nat av + total_arg_bytes_nat ev)%nat.
Proof.
intros av ev. unfold raw_len, cat_struct_size. rewrite !length_flatten_strings. reflexivity.
Qed.
Lemma pad_len_lt8 : forall av ev, (pad_len av ev < 8)%nat.
Proof.
intros av ev. unfold pad_len.
pose proof (Z.mod_pos_bound (8 - Z.of_nat (raw_len av ev) mod 8) 8 ltac:(lia)). lia.
Qed.
Lemma pad_aligns : forall n : Z, 0 <= n -> (n + (8 - n mod 8) mod 8) mod 8 = 0.
Proof.
intros n Hn.
pose proof (Z.div_mod n 8 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hr.
set (r := n mod 8) in *. set (q := n / 8) in *.
destruct (Z.eq_dec r 0) as [Hr0|Hr0].
- rewrite Hr0. change ((8 - 0) mod 8) with 0. rewrite Z.add_0_r. subst r. exact Hr0.
- rewrite (Z.mod_small (8 - r) 8) by lia.
replace (n + (8 - r)) with ((q + 1) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma rand_off_mod8 : forall av ev, Z.of_nat (rand_off av ev) mod 8 = 0.
Proof.
intros av ev. unfold rand_off, pad_len.
rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.mod_pos_bound; lia).
apply pad_aligns. lia.
Qed.
Section g.
Variable ph : PhdrInfo.
Variable sp : word.
Variable av ev : list (list byte).
Variable uid hw : word.
Variable rnd : EntryDraw.
Lemma bsb_decomp :
build_stack_bytes ph sp av ev uid hw rnd = cat_struct_prefix ph sp av ev uid hw ++ flatten_strings av ++ flatten_strings ev
++ repeat (Z_to_bv 8 0) (pad_len av ev) ++ at_random_bytes (ed_random rnd).
Proof.
unfold build_stack_bytes, cat_struct_prefix, cat_env_base, cat_string_base.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota zeta.
rewrite <- !app_assoc. do 8 f_equal.
f_equal. f_equal. unfold pad_len. f_equal. f_equal. f_equal. f_equal. f_equal.
rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst, !length_n_to_le_8,
length_auxv_bytes.
unfold raw_len. lia.
Qed.
End g.
Definition bytes_at (m : word -> option byte) (a : Z) (bs : list byte) : Prop :=
forall j, (j < length bs)%nat -> m (Z_to_bv 64 (a + Z.of_nat j)) = nth_error bs j.
Lemma bytes_at_app_inv : forall m a l1 l2,
bytes_at m a (l1 ++ l2) -> bytes_at m a l1 /\ bytes_at m (a + Z.of_nat (length l1)) l2.
Proof.
intros m a l1 l2 H. split; intros j Hj.
- rewrite <- (nth_error_app1 l1 l2 Hj). apply H. rewrite length_app. lia.
- rewrite <- (nth_error_app_off l1 l2 j).
replace (a + Z.of_nat (length l1) + Z.of_nat j) with (a + Z.of_nat (length l1 + j)) by lia.
apply H. rewrite length_app. lia.
Qed.
Lemma bytes_at_app_l : forall m a l1 l2, bytes_at m a (l1 ++ l2) -> bytes_at m a l1.
Proof. intros m a l1 l2 H. apply (bytes_at_app_inv m a l1 l2 H). Qed.
Lemma bytes_at_app_r : forall m a l1 l2,
bytes_at m a (l1 ++ l2) -> bytes_at m (a + Z.of_nat (length l1)) l2.
Proof. intros m a l1 l2 H. apply (bytes_at_app_inv m a l1 l2 H). Qed.
Lemma bytes_at_le8_nth : forall m a (l : list word) k,
bytes_at m a (flat_map word_le8 l) -> (k < length l)%nat ->
bytes_at m (a + 8 * Z.of_nat k) (word_le8 (nth k l (Z_to_bv 64 0))).
Proof.
intros m a l k H Hk j Hj. rewrite length_n_to_le_8 in Hj.
rewrite <- (nth_error_flat_map_le8 l k j Hk Hj).
replace (a + 8 * Z.of_nat k + Z.of_nat j) with (a + Z.of_nat (8 * k + j)) by lia.
apply H. rewrite length_flat_map_le8. lia.
Qed.
Lemma tab_firstn_S : forall (l : list (list byte)) k, (k < length l)%nat ->
(total_arg_bytes_nat (firstn (S k) l) = total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1)%nat.
Proof.
induction l as [|s l IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k].
- cbn [firstn nth]. rewrite total_arg_bytes_cons, firstn_O. change (total_arg_bytes_nat []) with 0%nat. lia.
- cbn [firstn nth]. rewrite !total_arg_bytes_cons. rewrite IH by (cbn in Hk; lia). lia.
Qed.
Lemma tab_firstn_nth_le : forall (l : list (list byte)) k, (k < length l)%nat ->
(total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= total_arg_bytes_nat l)%nat.
Proof.
intros l k Hk. rewrite <- tab_firstn_S by exact Hk. apply total_arg_bytes_firstn_le.
Qed.
Lemma bytes_at_strings_nth : forall m a (l : list (list byte)) k,
bytes_at m a (flatten_strings l) -> (k < length l)%nat ->
bytes_at m (a + Z.of_nat (total_arg_bytes_nat (firstn k l))) (nth k l [] ++ [Z_to_bv 8 0]).
Proof.
intros m a l k H Hk j Hj. rewrite length_app in Hj. cbn [length] in Hj.
rewrite <- (nth_error_flatten_strings l k j Hk ltac:(lia)).
replace (a + Z.of_nat (total_arg_bytes_nat (firstn k l)) + Z.of_nat j)
with (a + Z.of_nat (total_arg_bytes_nat (firstn k l) + j)) by lia.
apply H. rewrite length_flatten_strings. pose proof (tab_firstn_nth_le l k Hk). lia.
Qed.
Lemma bytes_at_frame : forall m m' a bs,
(forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> m' x = m x) ->
0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
bytes_at m a bs -> bytes_at m' a bs.
Proof.
intros m m' a bs Hfr Ha Hnw H j Hj. rewrite Hfr; [apply H; exact Hj|].
rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64). rewrite Z.mod_small by lia. lia.
Qed.
Lemma bytes_at_rdn : forall segs m a bs,
bytes_at m a bs -> rdn segs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
intros segs m a bs H. apply (proj2 (rdn_mbytes segs m (length bs) a bs)).
split; [reflexivity|]. intros i Hi. unfold mbyte. rewrite (H i Hi).
destruct (nth_error bs i) eqn:Hn; [reflexivity|].
exfalso. apply nth_error_None in Hn. lia.
Qed.
Lemma bytes_at_mbyte : forall segs m a bs j,
bytes_at m a bs -> (j < length bs)%nat ->
mbyte segs m (a + Z.of_nat j) = nth_error bs j.
Proof.
intros segs m a bs j H Hj. unfold mbyte. rewrite (H j Hj).
destruct (nth_error bs j) eqn:Hn; [reflexivity|].
exfalso. apply nth_error_None in Hn. lia.
Qed.
Lemma regions_wf_app : forall l1 l2, regions_wf (l1 ++ l2) = regions_wf l1 && regions_wf l2.
Proof. induction l1 as [|r l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma pairwise_disjoint_app : forall (En : env) l1 l2,
pairwise_disjoint En l1 -> pairwise_disjoint En l2 ->
(forall r1 r2, In r1 l1 -> In r2 l2 -> extent_disjoint En r1 r2) ->
pairwise_disjoint En (l1 ++ l2).
Proof.
intros En l1; induction l1 as [|r l1 IH]; intros l2 H1 H2 H12; cbn; [exact H2|].
destruct H1 as [Ha H1]. split.
- clear IH H1. induction l1 as [|r' l1 IH']; cbn in *.
+ clear Ha. induction l2 as [|r2 l2 IH2]; cbn; [exact I|]. split.
* apply H12; [left; reflexivity| left; reflexivity].
* apply IH2; [destruct H2; assumption|]. intros r1 r0 Hr1 Hr0. apply H12; [exact Hr1| right; exact Hr0].
+ destruct Ha as [Hrr' Ha]. split; [exact Hrr'|]. apply IH'; [exact Ha|].
intros r1 r2 Hr1 Hr2. apply H12; [destruct Hr1; [left|right;right]; assumption| exact Hr2].
- apply IH; [exact H1| exact H2|]. intros r1 r2 Hr1 Hr2. apply H12; [right; exact Hr1| exact Hr2].
Qed.
Lemma tget_empty : forall (A : Type) (p : positive), tget p (@TEmpty A) = None.
Proof. intros A p. destruct p; reflexivity. Qed.
Lemma mod8_of_mod16 : forall z k, z mod 16 = 0 -> (z + 8 * k) mod 8 = 0.
Proof.
intros z k Hz.
pose proof (Z.div_mod z 16 ltac:(lia)) as Hdm. rewrite Hz, Z.add_0_r in Hdm.
rewrite Hdm. replace (16 * (z / 16) + 8 * k) with ((2 * (z / 16) + k) * 8) by lia. apply Z_mod_mult.
Qed.
Definition z_envp (zsp : Z) (av : list (list byte)) : Z := zsp + 16 + 8 * Z.of_nat (length av).
Definition z_auxv (zsp : Z) (av ev : list (list byte)) : Z :=
z_envp zsp av + 8 * Z.of_nat (length ev) + 8.
Definition z_strs (zsp : Z) (av ev : list (list byte)) : Z := zsp + Z.of_nat (cat_struct_size av ev).
Definition z_argv (zsp : Z) (av ev : list (list byte)) (k : nat) : Z :=
z_strs zsp av ev + Z.of_nat (total_arg_bytes_nat (firstn k av)).
Definition z_envs (zsp : Z) (av ev : list (list byte)) (k : nat) : Z :=
z_strs zsp av ev + Z.of_nat (total_arg_bytes_nat av) + Z.of_nat (total_arg_bytes_nat (firstn k ev)).
Definition z_rand (zsp : Z) (av ev : list (list byte)) : Z := zsp + Z.of_nat (rand_off av ev).
Definition NUL : byte := Z_to_bv 8 0.
Definition E0 (sp : word) (av ev : list (list byte)) (xw : nat -> word) (xd : nat -> list byte) : env :=
let zsp := bv_unsigned sp in
mkEnv (fun n => match n with
| 0 => sp
| 1 => Z_to_bv 64 (z_argv zsp av ev 0)
| 2 => Z_to_bv 64 (z_argv zsp av ev 1)
| 3 => Z_to_bv 64 (Z.of_nat (length av))
| 4 => Z_to_bv 64 (z_envp zsp av)
| 5 => Z_to_bv 64 (z_auxv zsp av ev)
| 6 => Z_to_bv 64 (z_rand zsp av ev)
| _ => xw n
end)%nat
(fun d => match d with
| 0 => nth 0 av [] ++ [NUL]
| 1 => nth 1 av [] ++ [NUL]
| _ => xd d
end)%nat.
Definition UID_DATOM : nat := 4%nat.
Definition uid_bytes (uid : word) : list byte := word_le8 uid.
Definition HWCAP_DATOM : nat := 6%nat.
Definition hwcap_bytes (hw : word) : list byte := word_le8 hw.
Definition RAND_DATOM : nat := 7%nat.
Definition rand_bytes (rnd : EntryDraw) : list byte := at_random_bytes (ed_random rnd).
Lemma length_rand_bytes : forall rnd, length (rand_bytes rnd) = 16%nat.
Proof. intros rnd. reflexivity. Qed.
Lemma length_hwcap_bytes : forall hw, length (hwcap_bytes hw) = 8%nat.
Proof. intros hw. reflexivity. Qed.
Lemma length_uid_bytes : forall uid, length (uid_bytes uid) = 8%nat.
Proof. intros uid. reflexivity. Qed.
Definition auxv_chunks (ph : PhdrInfo) : list chunk :=
[ mkChunk 0 (CVal 8 (SLit 3));   mkChunk 8 (CVal 8 (SLit (Z.of_N (ph_addr ph))));
mkChunk 16 (CVal 8 (SLit 4));  mkChunk 24 (CVal 8 (SLit (Z.of_N (ph_ent ph))));
mkChunk 32 (CVal 8 (SLit 5));  mkChunk 40 (CVal 8 (SLit (Z.of_N (ph_num ph))));
mkChunk 48 (CVal 8 (SLit 16)); mkChunk 56 (CData HWCAP_DATOM 0 8);
mkChunk 64 (CVal 8 (SLit 6));  mkChunk 72 (CVal 8 (SLit 4096));
mkChunk 80 (CVal 8 (SLit 11)); mkChunk 88 (CData UID_DATOM 0 8);
mkChunk 96 (CVal 8 (SLit 12)); mkChunk 104 (CData UID_DATOM 0 8);
mkChunk 112 (CVal 8 (SLit 23)); mkChunk 120 (CVal 8 (SLit 0));
mkChunk 128 (CVal 8 (SLit 25)); mkChunk 136 (CVal 8 (SOff 6 0));
mkChunk 144 (CVal 8 (SLit 0)); mkChunk 152 (CVal 8 (SLit 0)) ].
Definition R_free (W : Z) : region :=
mkRegion (Some 0%nat) (-W) 0 (-W) 0 [mkChunk (-W) (CZero W)].
Definition R_hdr (two : bool) : region :=
mkRegion (Some 0%nat) 0 (if two then 24 else 16) 0 0
(mkChunk 0 (CVal 8 (SOff 3 0)) :: mkChunk 8 (CVal 8 (SOff 1 0))
:: if two then [mkChunk 16 (CVal 8 (SOff 2 0))] else []).
Definition R_argvnull : region := mkRegion (Some 4%nat) (-8) 0 0 0 [mkChunk (-8) (CVal 8 (SLit 0))].
Definition R_envnull : region := mkRegion (Some 5%nat) (-8) 0 0 0 [mkChunk (-8) (CVal 8 (SLit 0))].
Definition R_auxv (ph : PhdrInfo) : region := mkRegion (Some 5%nat) 0 160 0 0 (auxv_chunks ph).
Definition R_rand : region := mkRegion (Some 6%nat) 0 16 0 0 [mkChunk 0 (CData RAND_DATOM 0 16)].
Definition R_argv0 : region := mkRegion (Some 1%nat) 0 1 0 0 [mkChunk 0 (CData 0 0 1)].
Definition R_argv1 : region := mkRegion (Some 2%nat) 0 1 0 0 [mkChunk 0 (CData 1 0 1)].
Definition stack_regions (ph : PhdrInfo) (W : Z) (two : bool) : smem :=
R_free W :: R_hdr two :: R_argvnull :: R_envnull :: R_auxv ph :: R_rand :: R_argv0
:: (if two then [R_argv1] else []).
Definition K_stack : Z := 4194304.
Definition SP_LO : Z := 0x7fff80000000.
Definition SP_HI : Z := 0x800000000000.
Definition ptr_fact (al : Z) : afact := mkAF SP_LO (SP_HI - 16) al.
Definition G0 (two : bool) : facts :=
mkFacts [ (0%nat, mkAF SP_LO SP_HI 4);
(1%nat, ptr_fact 3);
(2%nat, ptr_fact 0);
(3%nat, mkAF (if two then 2 else 1) 1024 0);
(4%nat, ptr_fact 3);
(5%nat, ptr_fact 3);
(6%nat, ptr_fact 3) ] [] [].
Definition regs0 : list sv := [SLit 0; SLit 0; SOff 0 0].
Definition ss0 (pc : Z) (ph : PhdrInfo) (W : Z) (two : bool) (img : smem) : sstate :=
mkSS pc regs0 (stack_regions ph W two ++ img) None (G0 two).
Fixpoint zallb (f : Z -> bool) (a : Z) (n : nat) : bool :=
match n with O => true | S n' => f a && zallb f (a + 1) n' end.
Lemma zallb_sound : forall f n a x, zallb f a n = true -> a <= x < a + Z.of_nat n -> f x = true.
Proof.
induction n as [|n IH]; intros a x H Hx; [lia|].
cbn [zallb] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec x a) as [->|Hne]; [exact H1|].
apply (IH (a + 1)); [exact H2| lia].
Qed.
Definition img_limit : Z := SP_LO - 8388608.
Definition img_byte_ok (segs : list Segment) (a : Z) : bool :=
match img_byte segs a with Some _ => true | None => false end.
Definition img_zero_ok (segs : list Segment) (a : Z) : bool :=
match img_byte segs a with Some b => bv_eqb b (Z_to_bv 8 0) | None => false end.
Definition img_writable_ok (segs : list Segment) (a : Z) : bool :=
match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition img_chunk_ok (segs : list Segment) (c : chunk) : bool :=
match c_val c with
| CImg len => zallb (img_byte_ok segs) (c_off c) (Z.to_nat len)
| CZero len => zallb (img_zero_ok segs) (c_off c) (Z.to_nat len)
| _ => false
end.
Definition img_region_ok (segs : list Segment) (r : region) : bool :=
match r_base r with
| Some _ => false
| None => (0 <=? r_lo r) && (r_hi r <=? img_limit) && region_wf r
&& zallb (img_writable_ok segs) (r_wlo r) (Z.to_nat (r_whi r - r_wlo r))
&& forallb (img_chunk_ok segs) (r_chunks r)
end.
Definition img_disjoint (r r' : region) : bool := (r_hi r <=? r_lo r') || (r_hi r' <=? r_lo r).
Fixpoint img_pairwise (rs : smem) : bool :=
match rs with [] => true | r :: rs' => forallb (img_disjoint r) rs' && img_pairwise rs' end.
Definition img_check (segs : list Segment) (img : smem) : bool :=
forallb (img_region_ok segs) img && img_pairwise img.
Section h.
Variable segs : list Segment.
Lemma img_regions_base : forall img r,
forallb (img_region_ok segs) img = true -> In r img -> r_base r = None.
Proof.
intros img r H Hin. pose proof (proj1 (forallb_forall _ _) H r Hin) as Hr.
unfold img_region_ok in Hr. destruct (r_base r); [discriminate| reflexivity].
Qed.
Lemma img_regions_hi : forall img r,
forallb (img_region_ok segs) img = true -> In r img -> 0 <= r_lo r /\ r_hi r <= img_limit.
Proof.
intros img r H Hin. pose proof (proj1 (forallb_forall _ _) H r Hin) as Hr.
unfold img_region_ok in Hr. destruct (r_base r); [discriminate|].
rewrite !andb_true_iff in Hr. destruct Hr as [[[[H1 H2] _] _] _].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma img_regions_wf : forall img, forallb (img_region_ok segs) img = true -> regions_wf img = true.
Proof.
induction img as [|r img IH]; cbn; intros H; [reflexivity|].
apply andb_prop in H as [Hr H]. rewrite IH, andb_true_r by exact H.
unfold img_region_ok in Hr. destruct (r_base r); [discriminate|].
rewrite !andb_true_iff in Hr. tauto.
Qed.
Lemma img_pairwise_sound : forall (E : env) img,
forallb (img_region_ok segs) img = true -> img_pairwise img = true -> pairwise_disjoint E img.
Proof.
intros E. induction img as [|r img IH]; cbn; intros Hok H; [exact I|].
apply andb_prop in Hok as [Hr Hok]. apply andb_prop in H as [Hd H].
split; [|apply IH; assumption].
assert (Hb : r_base r = None) by (unfold img_region_ok in Hr; destruct (r_base r); [discriminate|reflexivity]).
clear IH H Hr. induction img as [|r' img IH']; cbn; [exact I|].
cbn in Hd. apply andb_prop in Hd as [Hrr' Hd]. cbn in Hok. apply andb_prop in Hok as [Hr' Hok].
split; [|apply IH'; assumption].
assert (Hb' : r_base r' = None) by (unfold img_region_ok in Hr'; destruct (r_base r'); [discriminate|reflexivity]).
unfold extent_disjoint. rewrite Hb, Hb'. cbn [base_val].
unfold img_disjoint in Hrr'. apply orb_prop in Hrr' as [Hx|Hx]; apply Z.leb_le in Hx; lia.
Qed.
End h.
Definition stack_tail (av ev : list (list byte)) (rnd : EntryDraw) : list byte :=
flatten_strings av ++ flatten_strings ev ++ repeat (Z_to_bv 8 0) (pad_len av ev) ++ rand_bytes rnd.
Section t.
Variable segs : list Segment.
Variable ph : PhdrInfo.
Variable sp : word.
Variable av ev : list (list byte).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hfits : entry_stack_fits sp av ev.
Variable uid hw : word.
Variable rnd : EntryDraw.
Local Abbreviation zsp := (bv_unsigned sp).
Local Abbreviation bsb := (build_stack_bytes ph sp av ev uid hw rnd).
Local Abbreviation esi := (entry_stack_image ph sp av ev uid hw rnd).
Local Abbreviation m0 := (wrap_mem ph sp av ev uid hw rnd).
Lemma zsp_lo : SP_LO <= zsp. Proof. exact (proj1 Hsp). Qed.
Lemma zsp_hi : zsp <= SP_HI. Proof. exact (proj1 (proj2 Hsp)). Qed.
Lemma zsp_al : zsp mod 16 = 0. Proof. exact (proj2 (proj2 Hsp)). Qed.
Lemma argc_bounds : 1 <= Z.of_nat (length av) <= 1024. Proof. exact (proj1 Hva). Qed.
Lemma envc_bound : Z.of_nat (length ev) <= 256. Proof. exact (proj1 Hve). Qed.
Lemma tab_av_bound : Z.of_nat (total_arg_bytes_nat av) <= 2097152.
Proof. rewrite <- total_arg_bytes_Z. exact (proj1 (proj2 Hva)). Qed.
Lemma tab_ev_bound : Z.of_nat (total_arg_bytes_nat ev) <= 131072.
Proof. rewrite <- total_arg_bytes_Z. exact (proj1 (proj2 Hve)). Qed.
Lemma struct_size_eq :
Z.of_nat (cat_struct_size av ev) = 184 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev).
Proof. unfold cat_struct_size, auxv_size. lia. Qed.
Lemma rand_off_eq :
Z.of_nat (rand_off av ev) = Z.of_nat (cat_struct_size av ev) + Z.of_nat (total_arg_bytes_nat av)
+ Z.of_nat (total_arg_bytes_nat ev) + Z.of_nat (pad_len av ev).
Proof. unfold rand_off. rewrite raw_len_eq. lia. Qed.
Lemma length_bsb : Z.of_nat (length bsb) = Z.of_nat (rand_off av ev) + 16.
Proof.
rewrite (bsb_decomp ph sp av ev uid hw rnd), !length_app, length_cat_struct_prefix,
!length_flatten_strings, repeat_length, length_at_random_bytes.
rewrite rand_off_eq. lia.
Qed.
Lemma rand_off_bound : Z.of_nat (rand_off av ev) <= 2239000.
Proof.
rewrite rand_off_eq, struct_size_eq.
pose proof argc_bounds. pose proof envc_bound. pose proof tab_av_bound. pose proof tab_ev_bound.
pose proof (pad_len_lt8 av ev). lia.
Qed.
Lemma bsb_end_bound : zsp + Z.of_nat (length bsb) < 2^63.
Proof.
rewrite length_bsb. pose proof rand_off_bound. pose proof zsp_hi. unfold SP_HI in *. lia.
Qed.
Lemma esi_eq : esi = bsb ++ entry_slack sp bsb (ed_slack rnd).
Proof. reflexivity. Qed.
Lemma esi_end : zsp + Z.of_nat (length esi) = entry_page_top sp bsb.
Proof. apply entry_stack_image_top. Qed.
Lemma length_esi_ge : (length bsb <= length esi)%nat.
Proof. rewrite esi_eq, length_app. lia. Qed.
Lemma esi_end_le : zsp + Z.of_nat (length esi) <= zsp + Z.of_nat (length bsb) + 4095.
Proof.
rewrite esi_end. unfold entry_page_top, page_round_up_Z, entry_block_top, page_size.
pose proof (Z.mul_div_le (bv_unsigned sp + Z.of_nat (length bsb) + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.
Lemma esi_end_bound : zsp + Z.of_nat (length esi) < 2^63.
Proof. pose proof esi_end_le. pose proof bsb_end_bound. pose proof rand_off_bound. pose proof zsp_hi.
rewrite length_bsb in *. unfold SP_HI in *. lia. Qed.
Lemma m0_image : bytes_at m0 zsp esi.
Proof.
intros j Hj. pose proof esi_end_bound as HB. pose proof (u64_range sp).
unfold wrap_mem, stack_to_mem.
rewrite u_Z2bv by lia.
replace (bv_unsigned sp <=? bv_unsigned sp + Z.of_nat j) with true by (symmetry; apply Z.leb_le; lia).
replace (bv_unsigned sp + Z.of_nat j - bv_unsigned sp <? Z.of_nat (length esi))
with true by (symmetry; apply Z.ltb_lt; lia).
replace (Z.to_nat (bv_unsigned sp + Z.of_nat j - bv_unsigned sp)) with j by lia.
destruct (nth_error _ j) eqn:Hn; [reflexivity|].
exfalso. apply nth_error_None in Hn. lia.
Qed.
Lemma m0_stack : bytes_at m0 zsp bsb.
Proof. pose proof m0_image as H. rewrite esi_eq in H. exact (bytes_at_app_l _ _ _ _ H). Qed.
Lemma m0_slack : bytes_at m0 (zsp + Z.of_nat (length bsb)) (entry_slack sp bsb (ed_slack rnd)).
Proof. pose proof m0_image as H. rewrite esi_eq in H. exact (bytes_at_app_r _ _ _ _ H). Qed.
Lemma m0_zero : forall x, zsp - stack_max_size <= x < zsp -> m0 (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
Proof.
intros x Hx. pose proof zsp_lo as HL. unfold SP_LO in HL. rewrite stack_max_size_val in Hx.
pose proof (u64_range sp).
unfold wrap_mem, stack_to_mem. rewrite u_Z2bv by lia.
replace (bv_unsigned sp <=? x) with false by (symmetry; apply Z.leb_gt; lia).
rewrite stack_max_size_val.
replace (bv_unsigned sp - 8388608 <=? x) with true by (symmetry; apply Z.leb_le; lia).
replace (x <? bv_unsigned sp) with true by (symmetry; apply Z.ltb_lt; lia).
reflexivity.
Qed.
Lemma m0_below : forall x, 0 <= x < zsp - stack_max_size -> m0 (Z_to_bv 64 x) = None.
Proof.
intros x Hx. pose proof stack_max_size_val. pose proof (u64_range sp).
apply wrap_mem_below. rewrite u_Z2bv by lia. lia.
Qed.
Lemma m0_above : forall x, zsp + Z.of_nat (length esi) <= x < 2^64 -> m0 (Z_to_bv 64 x) = None.
Proof.
intros x Hx. pose proof (u64_range sp).
unfold wrap_mem, stack_to_mem. rewrite u_Z2bv by lia.
replace (bv_unsigned sp <=? x) with true by (symmetry; apply Z.leb_le; lia).
replace (x - bv_unsigned sp <? Z.of_nat (length esi)) with false
by (symmetry; apply Z.ltb_ge; lia).
replace (x <? bv_unsigned sp) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite andb_false_r. reflexivity.
Qed.
Local Abbreviation argv_ptrs := (fst (string_addrs (cat_string_base sp av ev) av)).
Local Abbreviation envp_ptrs := (fst (string_addrs (cat_env_base sp av ev) ev)).
Lemma m0_argc : bytes_at m0 zsp (word_le8 (len_word av)).
Proof.
pose proof m0_stack as H. rewrite (bsb_decomp ph sp av ev uid hw rnd) in H.
unfold cat_struct_prefix in H. rewrite <- !app_assoc in H.
exact (bytes_at_app_l _ _ _ _ H).
Qed.
Lemma m0_argv_ptrs : bytes_at m0 (zsp + 8) (flat_map word_le8 argv_ptrs).
Proof.
pose proof m0_stack as H. rewrite (bsb_decomp ph sp av ev uid hw rnd) in H.
unfold cat_struct_prefix in H. rewrite <- !app_assoc in H.
apply bytes_at_app_r in H. rewrite length_n_to_le_8 in H.
exact (bytes_at_app_l _ _ _ _ H).
Qed.
Lemma m0_argv_null : bytes_at m0 (z_envp zsp av - 8) (word_le8 (Z_to_bv 64 0)).
Proof.
pose proof m0_stack as H. rewrite (bsb_decomp ph sp av ev uid hw rnd) in H.
unfold cat_struct_prefix in H. rewrite <- !app_assoc in H.
do 2 (apply bytes_at_app_r in H). apply bytes_at_app_l in H.
rewrite length_n_to_le_8, length_flat_map_le8 in H.
rewrite length_string_addrs_fst in H.
unfold z_envp. replace (zsp + 16 + 8 * Z.of_nat (length av) - 8)
with (zsp + Z.of_nat 8 + Z.of_nat (8 * length av)) by lia. exact H.
Qed.
Lemma m0_envp_ptrs : bytes_at m0 (z_envp zsp av) (flat_map word_le8 envp_ptrs).
Proof.
pose proof m0_stack as H. rewrite (bsb_decomp ph sp av ev uid hw rnd) in H.
unfold cat_struct_prefix in H. rewrite <- !app_assoc in H.
do 3 (apply bytes_at_app_r in H). apply bytes_at_app_l in H.
rewrite !length_n_to_le_8, length_flat_map_le8 in H.
rewrite length_string_addrs_fst in H.
unfold z_envp. replace (zsp + 16 + 8 * Z.of_nat (length av))
with (zsp + Z.of_nat 8 + Z.of_nat (8 * length av) + Z.of_nat 8) by lia. exact H.
Qed.
Lemma m0_envp_null : bytes_at m0 (z_auxv zsp av ev - 8) (word_le8 (Z_to_bv 64 0)).
Proof.
pose proof m0_stack as H. rewrite (bsb_decomp ph sp av ev uid hw rnd) in H.
unfold cat_struct_prefix in H. rewrite <- !app_assoc in H.
do 4 (apply bytes_at_app_r in H). apply bytes_at_app_l in H.
rewrite !length_n_to_le_8, !length_flat_map_le8 in H.
rewrite !length_string_addrs_fst in H.
unfold z_auxv, z_envp. replace (zsp + 16 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 8 - 8)
with (zsp + Z.of_nat 8 + Z.of_nat (8 * length av) + Z.of_nat 8 + Z.of_nat (8 * length ev)) by lia.
exact H.
Qed.
Lemma m0_auxv : bytes_at m0 (z_auxv zsp av ev)
(flat_map word_le8 (auxv_words (auxv_entries ph (at_random_ptr sp av ev) uid hw))).
Proof.
pose proof m0_stack as H. rewrite (bsb_decomp ph sp av ev uid hw rnd) in H.
unfold cat_struct_prefix in H. rewrite <- !app_assoc in H.
do 5 (apply bytes_at_app_r in H). apply bytes_at_app_l in H.
rewrite !length_n_to_le_8, !length_flat_map_le8 in H.
rewrite !length_string_addrs_fst in H.
unfold auxv_bytes in H. rewrite build_auxv_words in H.
unfold z_auxv, z_envp. replace (zsp + 16 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 8)
with (zsp + Z.of_nat 8 + Z.of_nat (8 * length av) + Z.of_nat 8 + Z.of_nat (8 * length ev) + Z.of_nat 8) by lia.
exact H.
Qed.
Lemma m0_tail : bytes_at m0 (z_strs zsp av ev) (stack_tail av ev rnd).
Proof.
pose proof m0_stack as H. rewrite (bsb_decomp ph sp av ev uid hw rnd) in H.
apply bytes_at_app_r in H. rewrite length_cat_struct_prefix in H. exact H.
Qed.
Lemma stack_tail_end : z_strs zsp av ev + Z.of_nat (length (stack_tail av ev rnd)) = z_rand zsp av ev + 16.
Proof.
unfold stack_tail. rewrite !length_app, !length_flatten_strings, repeat_length, length_rand_bytes.
unfold z_rand, z_strs. rewrite rand_off_eq. lia.
Qed.
Lemma m0_argv_strs : bytes_at m0 (z_strs zsp av ev) (flatten_strings av).
Proof.
pose proof m0_stack as H. rewrite (bsb_decomp ph sp av ev uid hw rnd) in H.
apply bytes_at_app_r in H. apply bytes_at_app_l in H.
rewrite length_cat_struct_prefix in H. exact H.
Qed.
Lemma m0_envp_strs : bytes_at m0 (z_strs zsp av ev + Z.of_nat (total_arg_bytes_nat av)) (flatten_strings ev).
Proof.
pose proof m0_stack as H. rewrite (bsb_decomp ph sp av ev uid hw rnd) in H.
do 2 (apply bytes_at_app_r in H). apply bytes_at_app_l in H.
rewrite length_cat_struct_prefix, length_flatten_strings in H. exact H.
Qed.
Lemma m0_rand : bytes_at m0 (z_rand zsp av ev) (rand_bytes rnd).
Proof.
pose proof m0_stack as H. rewrite (bsb_decomp ph sp av ev uid hw rnd) in H.
do 4 (apply bytes_at_app_r in H).
rewrite length_cat_struct_prefix, !length_flatten_strings, repeat_length in H.
unfold z_rand. rewrite rand_off_eq.
replace (zsp + (Z.of_nat (cat_struct_size av ev) + Z.of_nat (total_arg_bytes_nat av) +
Z.of_nat (total_arg_bytes_nat ev) + Z.of_nat (pad_len av ev)))
with (zsp + Z.of_nat (cat_struct_size av ev) + Z.of_nat (total_arg_bytes_nat av)
+ Z.of_nat (total_arg_bytes_nat ev) + Z.of_nat (pad_len av ev)) by lia.
exact H.
Qed.
Lemma u_cat_string_base : bv_unsigned (cat_string_base sp av ev) = z_strs zsp av ev.
Proof.
unfold cat_string_base, z_strs. rewrite word_add_nat.
pose proof rand_off_bound. pose proof rand_off_eq. pose proof zsp_hi. pose proof (u64_range sp).
unfold SP_HI in *. apply u_Z2bv; lia.
Qed.
Lemma z_argv_end : forall k, (k < length av)%nat ->
z_argv zsp av ev k + Z.of_nat (length (nth k av [])) + 1
<= z_strs zsp av ev + Z.of_nat (total_arg_bytes_nat av).
Proof. intros k Hk. unfold z_argv. pose proof (tab_firstn_nth_le av k Hk). lia. Qed.
Lemma z_envs_end : forall k, (k < length ev)%nat ->
z_envs zsp av ev k + Z.of_nat (length (nth k ev [])) + 1 <= z_rand zsp av ev.
Proof.
intros k Hk. unfold z_envs, z_rand, z_strs. rewrite rand_off_eq.
pose proof (tab_firstn_nth_le ev k Hk). lia.
Qed.
Lemma z_rand_end : z_rand zsp av ev + 16 < 2^63.
Proof. unfold z_rand. pose proof rand_off_bound. pose proof zsp_hi. unfold SP_HI in *. lia. Qed.
Lemma z_strs_rand : z_strs zsp av ev + Z.of_nat (total_arg_bytes_nat av) + Z.of_nat (total_arg_bytes_nat ev)
<= z_rand zsp av ev.
Proof. unfold z_strs, z_rand. rewrite rand_off_eq. lia. Qed.
Lemma block_fits : z_rand zsp av ev + 16 <= SP_HI.
Proof.
unfold z_rand. rewrite rand_off_eq, struct_size_eq. pose proof (pad_len_lt8 av ev).
pose proof Hfits as HF. unfold entry_stack_fits, entry_stack_span, auxv_size in HF.
rewrite !total_arg_bytes_Z in HF. change sp_window_hi with SP_HI in HF. lia.
Qed.
Lemma bsb_fits : zsp + Z.of_nat (length bsb) <= SP_HI.
Proof. rewrite length_bsb. pose proof block_fits as H. unfold z_rand in H. lia. Qed.
Lemma z_argv_fits : forall k, (k < length av)%nat ->
z_argv zsp av ev k + Z.of_nat (length (nth k av [])) + 1 <= SP_HI - 16.
Proof. intros k Hk. pose proof (z_argv_end k Hk). pose proof z_strs_rand. pose proof block_fits. lia. Qed.
Lemma z_envs_fits : forall k, (k < length ev)%nat ->
z_envs zsp av ev k + Z.of_nat (length (nth k ev [])) + 1 <= SP_HI - 16.
Proof. intros k Hk. pose proof (z_envs_end k Hk). pose proof block_fits. lia. Qed.
Lemma u_argv_ptr : forall k, (k < length av)%nat ->
nth k argv_ptrs (Z_to_bv 64 0) = Z_to_bv 64 (z_argv zsp av ev k).
Proof.
intros k Hk. rewrite nth_string_addrs by exact Hk.
rewrite word_add_nat, u_cat_string_base. reflexivity.
Qed.
Lemma u_envp_ptr : forall k, (k < length ev)%nat ->
nth k envp_ptrs (Z_to_bv 64 0) = Z_to_bv 64 (z_envs zsp av ev k).
Proof.
intros k Hk. rewrite nth_string_addrs by exact Hk.
unfold cat_env_base. rewrite !word_add_nat, u_cat_string_base.
pose proof z_strs_rand. pose proof z_rand_end. pose proof zsp_lo. unfold z_strs, SP_LO in *.
rewrite u_Z2bv by lia. reflexivity.
Qed.
Lemma m0_argv_ptr : forall k, (k < length av)%nat ->
bytes_at m0 (zsp + 8 + 8 * Z.of_nat k) (word_le8 (Z_to_bv 64 (z_argv zsp av ev k))).
Proof.
intros k Hk. rewrite <- u_argv_ptr by exact Hk. apply bytes_at_le8_nth; [exact m0_argv_ptrs|].
rewrite length_string_addrs_fst. exact Hk.
Qed.
Lemma m0_envp_ptr : forall k, (k < length ev)%nat ->
bytes_at m0 (z_envp zsp av + 8 * Z.of_nat k) (word_le8 (Z_to_bv 64 (z_envs zsp av ev k))).
Proof.
intros k Hk. rewrite <- u_envp_ptr by exact Hk. apply bytes_at_le8_nth; [exact m0_envp_ptrs|].
rewrite length_string_addrs_fst. exact Hk.
Qed.
Lemma m0_argv_str : forall k, (k < length av)%nat ->
bytes_at m0 (z_argv zsp av ev k) (nth k av [] ++ [NUL]).
Proof. intros k Hk. unfold z_argv. apply bytes_at_strings_nth; [exact m0_argv_strs| exact Hk]. Qed.
Lemma m0_envp_str : forall k, (k < length ev)%nat ->
bytes_at m0 (z_envs zsp av ev k) (nth k ev [] ++ [NUL]).
Proof. intros k Hk. unfold z_envs. apply bytes_at_strings_nth; [exact m0_envp_strs| exact Hk]. Qed.
Definition auxv_wordlist : list word := auxv_words (auxv_entries ph (at_random_ptr sp av ev) uid hw).
Lemma m0_auxv_word : forall e, (e < 20)%nat ->
bytes_at m0 (z_auxv zsp av ev + 8 * Z.of_nat e) (word_le8 (nth e auxv_wordlist (Z_to_bv 64 0))).
Proof. intros e He. apply bytes_at_le8_nth; [exact m0_auxv| exact He]. Qed.
Lemma at_random_ptr_val : at_random_ptr sp av ev = Z_to_bv 64 (z_rand zsp av ev).
Proof. rewrite at_random_ptr_eq, word_add_nat. reflexivity. Qed.
Lemma zsp_pos : 0 <= zsp. Proof. pose proof zsp_lo. unfold SP_LO in *. lia. Qed.
Lemma layout_facts :
z_envp zsp av = zsp + 16 + 8 * Z.of_nat (length av)
/\ z_auxv zsp av ev = z_envp zsp av + 8 * Z.of_nat (length ev) + 8
/\ z_strs zsp av ev = z_auxv zsp av ev + 160
/\ z_argv zsp av ev 0 = z_strs zsp av ev
/\ z_strs zsp av ev + Z.of_nat (total_arg_bytes_nat av) + Z.of_nat (total_arg_bytes_nat ev)
<= z_rand zsp av ev
/\ z_rand zsp av ev + 16 < 2^63
/\ SP_LO <= zsp <= SP_HI.
Proof.
pose proof struct_size_eq. pose proof z_strs_rand. pose proof z_rand_end. pose proof zsp_lo. pose proof zsp_hi.
unfold z_argv. rewrite firstn_O. change (total_arg_bytes_nat []) with 0%nat.
unfold z_auxv, z_envp, z_strs in *. repeat split; lia.
Qed.
Lemma argv_no_nul : forall k, (k < length av)%nat -> ~ In NUL (nth k av []).
Proof. intros k Hk. apply valid_argv_str_nz; [exact Hva| exact Hk]. Qed.
Lemma envp_no_nul : forall k, (k < length ev)%nat -> ~ In NUL (nth k ev []).
Proof.
intros k Hk. destruct Hve as (_ & _ & _ & Hnz). rewrite Forall_forall in Hnz.
apply Hnz. apply nth_In. exact Hk.
Qed.
Lemma argv_str_len : forall k, (k < length av)%nat -> Z.of_nat (length (nth k av [])) <= 131071.
Proof. intros k Hk. apply valid_argv_str_len; [exact Hva| exact Hk]. Qed.
Lemma z_argv_bounds : forall k, (k < length av)%nat ->
z_strs zsp av ev <= z_argv zsp av ev k
/\ z_argv zsp av ev k + Z.of_nat (length (nth k av [])) + 1
<= z_strs zsp av ev + Z.of_nat (total_arg_bytes_nat av).
Proof. intros k Hk. split; [unfold z_argv; lia| apply z_argv_end; exact Hk]. Qed.
Lemma z_envs_bounds : forall k, (k < length ev)%nat ->
z_strs zsp av ev + Z.of_nat (total_arg_bytes_nat av) <= z_envs zsp av ev k
/\ z_envs zsp av ev k + Z.of_nat (length (nth k ev [])) + 1 <= z_rand zsp av ev.
Proof. intros k Hk. split; [unfold z_envs; lia| apply z_envs_end; exact Hk]. Qed.
Lemma envp_ptr_nonzero : forall k, (k < length ev)%nat ->
Z_to_bv 64 (z_envs zsp av ev k) <> Z_to_bv 64 0.
Proof.
intros k Hk Heq. apply (f_equal bv_unsigned) in Heq.
pose proof (z_envs_bounds k Hk). pose proof layout_facts. unfold SP_LO in *.
rewrite u_Z2bv in Heq by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Heq. lia.
Qed.
Lemma init_argv_ptr_rdn : forall k, (k < length av)%nat ->
rdn segs m0 (Z_to_bv 64 (zsp + 8 + 8 * Z.of_nat k)) 8 = Some (word_le8 (Z_to_bv 64 (z_argv zsp av ev k))).
Proof. intros k Hk. apply (bytes_at_rdn segs m0 _ (word_le8 _)). apply m0_argv_ptr. exact Hk. Qed.
Lemma init_argv_cstr_rdn : forall k, (k < length av)%nat ->
rdn segs m0 (Z_to_bv 64 (z_argv zsp av ev k)) (length (nth k av []) + 1) = Some (nth k av [] ++ [NUL]).
Proof.
intros k Hk. replace (length (nth k av []) + 1)%nat with (length (nth k av [] ++ [NUL]))
by (rewrite length_app; reflexivity).
apply bytes_at_rdn. apply m0_argv_str. exact Hk.
Qed.
Lemma init_envp_ptr_rdn : forall k, (k < length ev)%nat ->
rdn segs m0 (Z_to_bv 64 (z_envp zsp av + 8 * Z.of_nat k)) 8
= Some (word_le8 (Z_to_bv 64 (z_envs zsp av ev k))).
Proof. intros k Hk. apply (bytes_at_rdn segs m0 _ (word_le8 _)). apply m0_envp_ptr. exact Hk. Qed.
Lemma init_envp_null_rdn :
rdn segs m0 (Z_to_bv 64 (z_envp zsp av + 8 * Z.of_nat (length ev))) 8 = Some (word_le8 (Z_to_bv 64 0)).
Proof.
pose proof layout_facts.
replace (z_envp zsp av + 8 * Z.of_nat (length ev)) with (z_auxv zsp av ev - 8) by lia.
apply (bytes_at_rdn segs m0 _ (word_le8 _)). apply m0_envp_null.
Qed.
Lemma init_envp_cstr_rdn : forall k, (k < length ev)%nat ->
rdn segs m0 (Z_to_bv 64 (z_envs zsp av ev k)) (length (nth k ev []) + 1) = Some (nth k ev [] ++ [NUL]).
Proof.
intros k Hk. replace (length (nth k ev []) + 1)%nat with (length (nth k ev [] ++ [NUL]))
by (rewrite length_app; reflexivity).
apply bytes_at_rdn. apply m0_envp_str. exact Hk.
Qed.
Variable W : Z.
Hypothesis HW : 0 < W <= 8388608.
Lemma regions_wf_stack : forall two, regions_wf (stack_regions ph W two) = true.
Proof.
intros two. unfold stack_regions. cbn [regions_wf].
replace (region_wf (R_free W)) with true.
2:{ symmetry. unfold region_wf, R_free, chunk_inside, c_len, cv_len;
cbn [r_lo r_hi r_wlo r_whi r_chunks forallb c_off c_val].
rewrite !andb_true_iff, !orb_true_iff, !Z.leb_le. lia. }
destruct two; reflexivity.
Qed.
Variable xw : nat -> word.
Variable xd : nat -> list byte.
Hypothesis Hxd : xd UID_DATOM = uid_bytes uid.
Hypothesis Hxh : xd HWCAP_DATOM = hwcap_bytes hw.
Hypothesis Hxr : xd RAND_DATOM = rand_bytes rnd.
Local Abbreviation E := (E0 sp av ev xw xd).
Lemma ed_uid : ed E UID_DATOM = word_le8 uid.
Proof. cbn [ed E0]. exact Hxd. Qed.
Lemma ed_hwcap : ed E HWCAP_DATOM = word_le8 hw.
Proof. cbn [ed E0]. exact Hxh. Qed.
Lemma ed_rand : ed E RAND_DATOM = rand_bytes rnd.
Proof. cbn [ed E0]. exact Hxr. Qed.
Lemma ew0 : bv_unsigned (ew E 0) = zsp. Proof. reflexivity. Qed.
Lemma ew1 : bv_unsigned (ew E 1) = z_strs zsp av ev.
Proof.
cbn [ew E E0]. unfold z_argv. rewrite firstn_O. change (total_arg_bytes_nat []) with 0%nat.
pose proof z_strs_rand. pose proof z_rand_end. pose proof zsp_pos. unfold z_strs in *.
rewrite u_Z2bv by lia. lia.
Qed.
Lemma ew2 : bv_unsigned (ew E 2) = z_strs zsp av ev + Z.of_nat (length (nth 0 av [])) + 1.
Proof.
cbn [ew E E0]. pose proof argc_bounds.
pose proof (z_argv_end 0 ltac:(lia)). pose proof z_strs_rand. pose proof z_rand_end. pose proof zsp_pos.
replace (z_argv (bv_unsigned sp) av ev 1) with (z_argv (bv_unsigned sp) av ev 0 + Z.of_nat (length (nth 0 av [])) + 1)
by (unfold z_argv; rewrite (tab_firstn_S av 0) by lia; lia).
unfold z_argv, z_strs in *. rewrite firstn_O in *. change (total_arg_bytes_nat []) with 0%nat in *.
rewrite u_Z2bv by lia. lia.
Qed.
Lemma ew2' : (2 <= length av)%nat -> bv_unsigned (ew E 2) = z_argv zsp av ev 1.
Proof.
intros H2. rewrite ew2. unfold z_argv. rewrite (tab_firstn_S av 0) by lia.
rewrite firstn_O. change (total_arg_bytes_nat []) with 0%nat. lia.
Qed.
Lemma ew3 : bv_unsigned (ew E 3) = Z.of_nat (length av).
Proof. cbn [ew E E0]. pose proof argc_bounds. apply u_Z2bv; lia. Qed.
Lemma ew4 : bv_unsigned (ew E 4) = z_envp zsp av.
Proof.
cbn [ew E E0]. pose proof z_strs_rand. pose proof z_rand_end. pose proof zsp_pos.
pose proof struct_size_eq. pose proof envc_bound. unfold z_strs, z_envp in *.
apply u_Z2bv; lia.
Qed.
Lemma ew5 : bv_unsigned (ew E 5) = z_auxv zsp av ev.
Proof.
cbn [ew E E0]. pose proof z_strs_rand. pose proof z_rand_end. pose proof zsp_pos.
pose proof struct_size_eq. unfold z_strs, z_auxv, z_envp in *.
apply u_Z2bv; lia.
Qed.
Lemma ew6 : bv_unsigned (ew E 6) = z_rand zsp av ev.
Proof.
cbn [ew E E0]. pose proof z_rand_end. pose proof zsp_pos. unfold z_rand in *.
apply u_Z2bv; lia.
Qed.
Lemma ew6_word : ew E 6 = at_random_ptr sp av ev.
Proof. rewrite at_random_ptr_val. reflexivity. Qed.
Lemma ed0 : ed E 0 = nth 0 av [] ++ [NUL]. Proof. reflexivity. Qed.
Lemma ed1 : ed E 1 = nth 1 av [] ++ [NUL]. Proof. reflexivity. Qed.
Lemma chunk_ok_word : forall m base off v (w : word),
sv_denot E v = w -> bytes_at m (base + off) (word_le8 w) ->
chunk_ok segs E m base (mkChunk off (CVal 8 v)).
Proof.
intros m base off v w Hv Hb i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (byte_of_word w i). split; [rewrite Hv; reflexivity|].
replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (bytes_at_mbyte segs m (base + off) (word_le8 w) (Z.to_nat i) Hb)
by (rewrite length_n_to_le_8; lia).
apply word_le8_nth. lia.
Qed.
Lemma chunk_ok_zero : forall m base off len,
(forall i, 0 <= i < len -> m (Z_to_bv 64 (base + off + i)) = Some (Z_to_bv 8 0)) ->
chunk_ok segs E m base (mkChunk off (CZero len)).
Proof.
intros m base off len H i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (Z_to_bv 8 0). split; [reflexivity|]. unfold mbyte. rewrite H by exact Hi. reflexivity.
Qed.
Lemma chunk_ok_data1 : forall m base off d s,
bytes_at m (base + off) [nth s (ed E d) NUL] -> (s < length (ed E d))%nat ->
chunk_ok segs E m base (mkChunk off (CData d (Z.of_nat s) 1)).
Proof.
intros m base off d s Hb Hs i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (nth s (ed E d) NUL). split.
- replace (Z.to_nat (Z.of_nat s + i)) with s by lia. apply nth_error_nth'. exact Hs.
- replace i with (Z.of_nat 0) by lia. apply (bytes_at_mbyte segs m (base + off) [nth s (ed E d) NUL] 0 Hb).
cbn. lia.
Qed.
Lemma chunk_ok_data8 : forall m base off d (w : word),
ed E d = word_le8 w -> bytes_at m (base + off) (word_le8 w) ->
chunk_ok segs E m base (mkChunk off (CData d 0 8)).
Proof.
intros m base off d w Hd Hb i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
rewrite Hd. exists (byte_of_word w i). split.
- rewrite Z.add_0_l. replace (Z.to_nat i) with (Z.to_nat i) by reflexivity.
rewrite word_le8_nth by lia. f_equal. f_equal. lia.
- replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (bytes_at_mbyte segs m (base + off) (word_le8 w) (Z.to_nat i) Hb)
by (rewrite length_n_to_le_8; lia).
apply word_le8_nth. lia.
Qed.
Lemma chunk_ok_data : forall m base off d bs,
ed E d = bs -> bytes_at m (base + off) bs ->
chunk_ok segs E m base (mkChunk off (CData d 0 (Z.of_nat (length bs)))).
Proof.
intros m base off d bs Hd Hb i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
rewrite Hd, Z.add_0_l.
destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn;
[| exfalso; apply nth_error_None in Hn; lia].
exists b. split; [reflexivity|].
replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (bytes_at_mbyte segs m (base + off) bs (Z.to_nat i) Hb) by lia. exact Hn.
Qed.
Lemma region_ok_free : region_ok segs E m0 (R_free W).
Proof.
unfold region_ok, R_free; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew0.
pose proof zsp_lo. pose proof zsp_hi. unfold SP_LO, SP_HI in *. pose proof stack_max_size_val.
split; [lia|]. split; [lia|]. split.
- intros o Ho. unfold writable_at, wview. rewrite m0_zero by lia. discriminate.
- constructor; [|constructor]. apply chunk_ok_zero. intros i Hi. apply m0_zero. lia.
Qed.
Lemma sv_denot_SOff0 : forall n, sv_denot E (SOff n 0) = ew E n.
Proof. intros n. cbn. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma region_ok_hdr : forall two : bool,
(if two then 2 <= length av else True)%nat -> region_ok segs E m0 (R_hdr two).
Proof.
intros two Htwo.
unfold region_ok, R_hdr; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew0.
pose proof zsp_lo. pose proof zsp_hi. unfold SP_LO, SP_HI in *. pose proof argc_bounds.
split; [lia|]. split; [destruct two; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
- apply (chunk_ok_word _ _ _ _ (len_word av)).
+ rewrite sv_denot_SOff0. apply bv_eq. rewrite ew3. unfold len_word. symmetry. apply u_Z2bv; lia.
+ rewrite Z.add_0_r. exact m0_argc.
- apply (chunk_ok_word _ _ _ _ (Z_to_bv 64 (z_argv zsp av ev 0))).
+ rewrite sv_denot_SOff0. reflexivity.
+ replace (zsp + 8) with (zsp + 8 + 8 * Z.of_nat 0) by lia. apply m0_argv_ptr. lia.
- destruct two; [|constructor]. constructor; [|constructor].
apply (chunk_ok_word _ _ _ _ (Z_to_bv 64 (z_argv zsp av ev 1))).
+ rewrite sv_denot_SOff0. reflexivity.
+ replace (zsp + 16) with (zsp + 8 + 8 * Z.of_nat 1) by lia. apply m0_argv_ptr. lia.
Qed.
Lemma region_ok_argvnull : region_ok segs E m0 R_argvnull.
Proof.
unfold region_ok, R_argvnull; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew4.
pose proof layout_facts. pose proof argc_bounds. unfold SP_LO, SP_HI in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_word _ _ _ _ (Z_to_bv 64 0)); [reflexivity|].
replace (z_envp zsp av + -8) with (z_envp zsp av - 8) by lia. exact m0_argv_null.
Qed.
Lemma region_ok_envnull : region_ok segs E m0 R_envnull.
Proof.
unfold region_ok, R_envnull; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew5.
pose proof layout_facts. pose proof argc_bounds. pose proof envc_bound. unfold SP_LO, SP_HI in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_word _ _ _ _ (Z_to_bv 64 0)); [reflexivity|].
replace (z_auxv zsp av ev + -8) with (z_auxv zsp av ev - 8) by lia. exact m0_envp_null.
Qed.
Lemma region_ok_auxv : region_ok segs E m0 (R_auxv ph).
Proof.
unfold region_ok, R_auxv; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew5.
pose proof layout_facts. pose proof argc_bounds. pose proof envc_bound. unfold SP_LO, SP_HI in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold auxv_chunks.
repeat match goal with
| |- Forall _ [] => constructor
| |- Forall _ (mkChunk ?off (CData _ _ _) :: _) =>
constructor;
[ apply (chunk_ok_data8 _ _ _ _ (nth (Z.to_nat (off / 8)) auxv_wordlist (Z_to_bv 64 0)));
[ first [exact ed_uid | exact ed_hwcap]
| replace (z_auxv zsp av ev + off) with (z_auxv zsp av ev + 8 * Z.of_nat (Z.to_nat (off / 8)))
by (clear; cbn; lia);
apply m0_auxv_word; clear; cbn; lia ]
| ]
| |- Forall _ (mkChunk ?off _ :: _) =>
constructor;
[ apply (chunk_ok_word _ _ _ _ (nth (Z.to_nat (off / 8)) auxv_wordlist (Z_to_bv 64 0)));
[ | replace (z_auxv zsp av ev + off) with (z_auxv zsp av ev + 8 * Z.of_nat (Z.to_nat (off / 8)))
by (clear; cbn; lia);
apply m0_auxv_word; clear; cbn; lia ]
| ]
end.
all: try reflexivity.
rewrite sv_denot_SOff0, ew6_word. reflexivity.
Qed.
Lemma region_ok_rand : region_ok segs E m0 R_rand.
Proof.
unfold region_ok, R_rand; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew6.
pose proof layout_facts. unfold SP_LO, SP_HI in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
change 16 with (Z.of_nat (length (rand_bytes rnd))). apply chunk_ok_data; [exact ed_rand|].
rewrite Z.add_0_r. exact m0_rand.
Qed.
Lemma region_ok_argv0 : region_ok segs E m0 R_argv0.
Proof.
unfold region_ok, R_argv0; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew1.
pose proof layout_facts. pose proof argc_bounds. unfold SP_LO, SP_HI in *.
pose proof (z_argv_end 0 ltac:(lia)).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
change (CData 0 0 1) with (CData 0 (Z.of_nat 0) 1). apply chunk_ok_data1.
- rewrite ed0, Z.add_0_r. intros j Hj. cbn in Hj.
pose proof (m0_argv_str 0 ltac:(lia)) as Hs. unfold z_argv in Hs. rewrite firstn_O in Hs.
change (total_arg_bytes_nat []) with 0%nat in Hs. rewrite Z.add_0_r in Hs.
rewrite (Hs j) by (rewrite length_app; cbn; lia).
destruct j; [|lia]. destruct (nth 0 av [] ++ [NUL]) eqn:Hn; [|reflexivity].
exfalso. destruct (nth 0 av []); discriminate.
- rewrite ed0, length_app. cbn. lia.
Qed.
Lemma region_ok_argv1 : (2 <= length av)%nat -> region_ok segs E m0 R_argv1.
Proof.
intros H2.
unfold region_ok, R_argv1; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite (ew2' H2).
pose proof layout_facts. unfold SP_LO, SP_HI in *.
pose proof (z_argv_end 1 ltac:(lia)).
assert (Hz0 : z_strs zsp av ev <= z_argv zsp av ev 1) by (unfold z_argv; lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
change (CData 1 0 1) with (CData 1 (Z.of_nat 0) 1). apply chunk_ok_data1.
- rewrite ed1, Z.add_0_r. intros j Hj. cbn in Hj.
pose proof (m0_argv_str 1 ltac:(lia)) as Hs.
rewrite (Hs j) by (rewrite length_app; cbn; lia).
destruct j; [|lia]. destruct (nth 1 av [] ++ [NUL]) eqn:Hn; [|reflexivity].
exfalso. destruct (nth 1 av []); discriminate.
- rewrite ed1, length_app. cbn. lia.
Qed.
Lemma pairwise_disjoint_stack : forall two : bool,
(if two then 2 <= length av else True)%nat ->
pairwise_disjoint E (stack_regions ph W two).
Proof.
intros two Htwo.
pose proof layout_facts as L. pose proof argc_bounds as HA. pose proof envc_bound as HE.
pose proof (z_argv_end 0 ltac:(lia)) as HZ0. pose proof ew2 as E2.
assert (E2' : two = true -> bv_unsigned (ew E 2) + Z.of_nat (length (nth 1 av [])) + 1
<= z_strs zsp av ev + Z.of_nat (total_arg_bytes_nat av)).
{ intros ->. rewrite (ew2' Htwo). apply z_argv_end. lia. }
unfold stack_regions. destruct two; cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint;
cbn [r_base r_lo r_hi R_free R_hdr R_argvnull R_envnull R_auxv R_rand R_argv0 R_argv1 base_val];
rewrite ?ew0, ?ew1, ?ew3, ?ew4, ?ew5, ?ew6 in *.
- specialize (E2' eq_refl). repeat split; lia.
- repeat split; lia.
Qed.
Lemma stack_regions_lo : forall two r, In r (stack_regions ph W two) ->
img_limit <= base_val E (r_base r) + r_lo r.
Proof.
intros two r Hin.
pose proof layout_facts as L. pose proof argc_bounds as HA. pose proof ew2 as E2.
unfold img_limit, SP_LO, SP_HI in *.
unfold stack_regions in Hin. cbn [In app] in Hin.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]
| In _ (if ?b then _ else _) => destruct b; cbn [In] in Hin
| False => destruct Hin
end;
cbn [r_base r_lo R_free R_hdr R_argvnull R_envnull R_auxv R_rand R_argv0 R_argv1 base_val];
rewrite ?ew0, ?ew1, ?ew3, ?ew4, ?ew5, ?ew6; lia.
Qed.
Lemma region_ok_img : forall r, img_region_ok segs r = true -> region_ok segs E m0 r.
Proof.
intros r H. unfold img_region_ok in H.
destruct (r_base r) as [n|] eqn:Hb; [discriminate|].
apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hw]. apply andb_prop in H as [H Hwf].
apply andb_prop in H as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
apply region_wf_facts in Hwf as (Hlohi & Hwr & Hci).
pose proof zsp_lo as HL. unfold img_limit, SP_LO in *. pose proof stack_max_size_val as HS.
unfold region_ok. rewrite Hb. cbn [base_val]. rewrite !Z.add_0_l.
split; [lia|]. split; [lia|]. split.
- intros o Ho. pose proof (zallb_sound _ _ _ o Hw ltac:(lia)) as Ho'. unfold img_writable_ok in Ho'.
unfold writable_at. rewrite Z.add_0_l.
apply (wview_grows segs (fun _ => None)); [intros x Hx; exfalso; apply Hx; reflexivity|].
destruct (wview segs (fun _ => None) (Z_to_bv 64 o)); [discriminate| discriminate Ho'].
- apply Forall_forall. intros c Hin.
pose proof (proj1 (forallb_forall _ _) Hc c Hin) as Hck.
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hin)) as (C1 & C2 & C3).
intros i Hi. unfold img_chunk_ok in Hck.
assert (Hm : m0 (Z_to_bv 64 (0 + c_off c + i)) = None).
{ apply m0_below. cbn [c_off c_len] in Hi. lia. }
unfold mbyte. rewrite Hm. rewrite Z.add_0_l in *.
unfold c_len in Hi.
destruct (c_val c) as [w v|len|len|d s len] eqn:Hcv; try discriminate Hck; cbn [cbyte cv_len] in Hi |- *.
+ pose proof (zallb_sound _ _ _ (c_off c + i) Hck ltac:(lia)) as Hz. unfold img_zero_ok, img_byte in Hz.
destruct (seg_rom segs (Z_to_bv 64 (c_off c + i))) as [b|]; [|discriminate].
exists (Z_to_bv 8 0). split; [reflexivity|]. f_equal.
unfold bv_eqb in Hz. apply Z.eqb_eq in Hz. apply bv_eq. exact Hz.
+ pose proof (zallb_sound _ _ _ (c_off c + i) Hck ltac:(lia)) as Hz. unfold img_byte_ok, img_byte in Hz.
unfold img_byte.
destruct (seg_rom segs (Z_to_bv 64 (c_off c + i))) as [b|]; [|discriminate].
exists b. split; reflexivity.
Qed.
Lemma regs_ok_init : regs_ok E regs0 (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp).
Proof.
intros r. unfold sr_get, regs0.
assert (Hsr : forall r' : reg, bv_unsigned r' <> 2 ->
sv_denot E (if bv_eqb r' 0 then SLit 0 else nth (ridx r') [SLit 0; SLit 0; SOff 0 0] (SLit 0))
= Z_to_bv 64 0).
{ intros r' Hr'. destruct (bv_eqb r' 0); [reflexivity|]. unfold ridx.
destruct (Z.to_nat (bv_unsigned r')) as [|[|[|k]]] eqn:Hk; try reflexivity; [exfalso; lia|].
destruct k; reflexivity. }
destruct (Z.eq_dec (bv_unsigned r) 2) as [Hr2|Hr2].
- assert (r = 2%bv) as -> by (apply bv_eq; exact Hr2).
rewrite getr_same by reg_neq_tac.
match goal with |- _ = sv_denot E ?v => replace v with (SOff 0 0) by reflexivity end.
symmetry. apply sv_denot_SOff0.
- rewrite Hsr by exact Hr2.
rewrite getr_other by (intros H; apply Hr2; rewrite H; reflexivity).
destruct (Z.eq_dec (bv_unsigned r) 10) as [Hr10|Hr10].
+ assert (r = 10%bv) as -> by (apply bv_eq; exact Hr10). rewrite getr_same by reg_neq_tac. reflexivity.
+ rewrite getr_other by (intros H; apply Hr10; rewrite H; reflexivity).
unfold getr. destruct (bv_eqb r 0); [reflexivity|].
unfold reg_get, bvmap_get, bvmap_empty. rewrite tget_empty. reflexivity.
Qed.
Lemma facts_ok_init : forall two : bool,
(if two then 2 <= length av else True)%nat -> facts_ok E (G0 two).
Proof.
intros two Htwo. unfold facts_ok, G0; cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; exact I].
pose proof layout_facts as L. pose proof argc_bounds as HA. pose proof envc_bound as HE.
pose proof rand_off_bound as HR. pose proof struct_size_eq as HS. pose proof zsp_al as HAL.
pose proof (rand_off_mod8 av ev) as HR8. pose proof block_fits as HF.
unfold afact_ok, ptr_fact; cbn [af_lo af_hi af_al2].
rewrite ew0, ew1, ew3, ew4, ew5, ew6.
change (2^4) with 16. change (2^3) with 8. change (2^0) with 1. rewrite !Z.mod_1_r.
unfold K_stack, SP_LO, SP_HI, z_rand, z_strs, z_auxv, z_envp in *.
assert (H8a : (zsp + Z.of_nat (cat_struct_size av ev)) mod 8 = 0).
{ rewrite HS. replace (zsp + (184 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)))
with (zsp + 8 * (23 + Z.of_nat (length av) + Z.of_nat (length ev))) by lia.
apply mod8_of_mod16. exact HAL. }
assert (H8b : (zsp + 16 + 8 * Z.of_nat (length av)) mod 8 = 0).
{ replace (zsp + 16 + 8 * Z.of_nat (length av)) with (zsp + 8 * (2 + Z.of_nat (length av))) by lia.
apply mod8_of_mod16. exact HAL. }
assert (H8c : (zsp + 16 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 8) mod 8 = 0).
{ replace (zsp + 16 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 8)
with (zsp + 8 * (3 + Z.of_nat (length av) + Z.of_nat (length ev))) by lia.
apply mod8_of_mod16. exact HAL. }
assert (H8d : (zsp + Z.of_nat (rand_off av ev)) mod 8 = 0).
{ rewrite <- Zplus_mod_idemp_r, HR8, Z.add_0_r.
replace zsp with (zsp + 8 * 0) by lia. apply mod8_of_mod16. exact HAL. }
pose proof ew2 as E2. unfold z_strs in E2.
pose proof (z_argv_end 0 ltac:(lia)) as HZ0. unfold z_argv, z_strs in HZ0.
rewrite firstn_O in HZ0. change (total_arg_bytes_nat []) with 0%nat in HZ0.
destruct two; repeat split; try lia.
Qed.
Theorem init_st_ok : forall (pc : N) (two : bool) (img : smem),
(if two then 2 <= length av else True)%nat ->
img_check segs img = true ->
@st_ok segs fx0 E (ss0 (Z.of_N pc) ph W two img) (init_machine_state segs pc ph sp rnd av ev uid hw).
Proof.
intros pc two img Htwo Himg. unfold img_check in Himg. apply andb_prop in Himg as [Hiok Hipw].
rewrite init_mkst. unfold st_ok, ss0, mkst;
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [apply regs_ok_init|].
split; [|apply facts_ok_init; exact Htwo].
split; [|split].
- rewrite regions_wf_app, regions_wf_stack, (img_regions_wf segs) by exact Hiok. reflexivity.
- apply Forall_app. split.
+ unfold stack_regions.
constructor; [apply region_ok_free|].
constructor; [apply region_ok_hdr; exact Htwo|].
constructor; [apply region_ok_argvnull|].
constructor; [apply region_ok_envnull|].
constructor; [apply region_ok_auxv|].
constructor; [apply region_ok_rand|].
constructor; [apply region_ok_argv0|].
destruct two; [|constructor]. constructor; [apply region_ok_argv1; exact Htwo| constructor].
+ apply Forall_forall. intros r Hin. apply region_ok_img.
exact (proj1 (forallb_forall _ _) Hiok r Hin).
- apply pairwise_disjoint_app.
+ apply pairwise_disjoint_stack. exact Htwo.
+ apply (img_pairwise_sound segs); assumption.
+ intros r1 r2 H1 H2. unfold extent_disjoint. right.
pose proof (stack_regions_lo two r1 H1).
pose proof (img_regions_hi segs img r2 Hiok H2) as [Hlo2 Hhi2].
rewrite (img_regions_base segs img r2 Hiok H2). cbn [base_val]. lia.
Qed.
Lemma afact_ok_argc : forall lo hi : Z,
lo <= Z.of_nat (length av) <= hi -> afact_ok E 3 (mkAF lo hi 0).
Proof.
intros lo hi H. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite ew3.
change (2^0) with 1. rewrite Z.mod_1_r. lia.
Qed.
Lemma sext32_argc : sv_denot E (SExt true 32 (SOff 3 0)) = sv_denot E (SOff 3 0).
Proof.
pose proof ew3 as H3. pose proof argc_bounds.
cbn [sv_denot]. rewrite Z.add_0_r, H3.
apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned.
unfold bv_signed. rewrite bv_extract_unsigned, Z.shiftr_0_r, !Z_to_bv_unsigned.
unfold bv_swrap, bv_wrap.
change (bv_modulus 64) with (2^64). change (bv_modulus 32) with (2^32).
change (bv_half_modulus 32) with (2^31).
rewrite (Z.mod_small (Z.of_nat (length av)) (2^64)) by lia.
rewrite (Z.mod_small (Z.of_nat (length av)) (2^32)) by lia.
rewrite (Z.mod_small (_ + 2^31) (2^32)) by lia.
rewrite ?Z.mod_small by lia. lia.
Qed.
End t.
Fixpoint cond_caps_whi (l : list acond) (n : nat) (whi lo hi : Z) : bool :=
match l with
| [] => false
| c :: l' =>
(match ac_c c, ac_a c, ac_b c with
| BC_GEU, SOff O 0, SOff m K =>
Nat.eqb m n && (whi <=? K) && (0 <=? lo + K) && (hi + K <? 2 ^ 64)
| _, _, _ => false
end) || cond_caps_whi l' n whi lo hi
end.
Definition wr_below_sp (G : facts) (rs : smem) : bool :=
match atom_lookup (f_atoms G) 0 with
| None => false
| Some f0 =>
forallb (fun r =>
(r_whi r <=? r_wlo r) ||
match r_base r with
| None => r_whi r <=? af_lo f0
| Some O => r_whi r <=? 0
| Some n => match atom_lookup (f_atoms G) n with
| Some f => (af_hi f + r_whi r <=? af_lo f0)
|| cond_caps_whi (f_conds G) n (r_whi r) (af_lo f) (af_hi f)
| None => false
end
end) rs
end.
Lemma acond_geu_sp_intro : forall E n K,
0 <= bv_unsigned (ew E n) + K <= bv_unsigned (ew E 0) ->
branch_taken BC_GEU (sv_denot E (SOff 0 0)) (sv_denot E (SOff n K)) = true.
Proof.
intros E n K HK. pose proof (u64_range (ew E 0)) as H0.
cbn [branch_taken sv_denot]. unfold bv_ltu. rewrite Z.add_0_r, !Z_to_bv_unsigned.
change (bv_wrap 64 ?x) with (x mod 2^64). rewrite !Z.mod_small by lia.
apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma cond_caps_whi_sound : forall E l n whi lo hi,
conds_ok E l -> cond_caps_whi l n whi lo hi = true ->
lo <= bv_unsigned (ew E n) <= hi ->
bv_unsigned (ew E n) + whi <= bv_unsigned (ew E 0).
Proof.
intros E l n whi lo hi. induction l as [|c l IH]; cbn [cond_caps_whi conds_ok]; intros Hok H Hn;
[discriminate|].
destruct Hok as [Hc Hl]. apply orb_prop in H as [H|H]; [|exact (IH Hl H Hn)]. clear IH Hl.
destruct c as [cc ca cb]; cbn [ac_c ac_a ac_b] in H. unfold acond_ok in Hc; cbn [ac_c ac_a ac_b] in Hc.
destruct cc; try discriminate H.
destruct ca as [|n0 z0| | | | | | | | |]; try discriminate H.
destruct n0; [|discriminate H]. destruct z0; try discriminate H.
destruct cb as [|m K| | | | | | | | |]; try discriminate H.
rewrite !andb_true_iff in H. destruct H as [[[Hm Hw] Hlo] Hhi].
apply Nat.eqb_eq in Hm. subst m. apply Z.leb_le in Hw. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
pose proof (u64_range (ew E 0)) as H0.
cbn [branch_taken sv_denot] in Hc. unfold bv_ltu in Hc. rewrite Z.add_0_r, !Z_to_bv_unsigned in Hc.
change (bv_wrap 64 ?x) with (x mod 2^64) in Hc. rewrite !Z.mod_small in Hc by lia.
apply negb_true_iff in Hc. apply Z.ltb_ge in Hc. lia.
Qed.
Lemma wr_below_sp_sound : forall E G rs x,
facts_ok E G -> wr_below_sp G rs = true -> in_wrange E rs x -> x < bv_unsigned (ew E 0).
Proof.
intros E G rs x HG H (r & Hin & Hx). unfold wr_below_sp in H.
destruct (atom_lookup (f_atoms G) 0) as [f0|] eqn:H0; [|discriminate].
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) H0) as (Hf0 & _).
pose proof (proj1 (forallb_forall _ _) H r Hin) as Hr. cbn beta in Hr.
apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
destruct (r_base r) as [[|n]|] eqn:Hb; cbn [base_val] in Hx.
- apply Z.leb_le in Hr. lia.
- destruct (atom_lookup (f_atoms G) (S n)) as [f|] eqn:Hn; [|discriminate].
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hn) as (Hf & _).
apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
pose proof (cond_caps_whi_sound E (f_conds G) (S n) (r_whi r) (af_lo f) (af_hi f)
(proj1 (proj2 HG)) Hr Hf). lia.
- apply Z.leb_le in Hr. lia.
Qed.
Lemma bytes_at_frame_sp : forall E G rs m m' a bs,
facts_ok E G -> wr_below_sp G rs = true -> frame_of E rs m m' ->
bv_unsigned (ew E 0) <= a -> a + Z.of_nat (length bs) <= 2^64 ->
bytes_at m a bs -> bytes_at m' a bs.
Proof.
intros E G rs m m' a bs HG Hw Hfr Ha Hnw H.
pose proof (u64_range (ew E 0)).
apply (bytes_at_frame m m' a bs); [|lia|exact Hnw|exact H].
intros x Hx. apply Hfr. intros Hin. pose proof (wr_below_sp_sound E G rs _ HG Hw Hin). lia.
Qed.
