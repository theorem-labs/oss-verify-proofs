(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3u.v, with its module paths changed. *)
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
Lemma shiftr_bytes_le_mod256 : forall (bs : list byte) i, (i < length bs)%nat ->
(Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat i)) mod 2 ^ 8 = bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b bs IH]; intros i Hi; [cbn in Hi; lia|].
pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with (2 ^ 8) in Hb.
pose proof (bytes_le_to_Z_nonneg (b :: bs)) as Hnn. pose proof (bytes_le_to_Z_nonneg bs) as Hnn'.
cbn [length] in Hi.
apply Z.bits_inj'. intros k Hk.
destruct (Z_lt_le_dec k 8) as [Hk8|Hk8].
- rewrite Z.mod_pow2_bits_low, Z.shiftr_spec by lia.
rewrite testbit_bytes_le_cons by lia.
destruct i as [|i]; cbn [nth].
+ replace (k + 8 * Z.of_nat 0%nat <? 8) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. lia.
+ replace (k + 8 * Z.of_nat (S i) <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite <- (IH i) by lia.
rewrite Z.mod_pow2_bits_low, Z.shiftr_spec by lia. f_equal. lia.
- rewrite Z.mod_pow2_bits_high by lia. symmetry.
pose proof (bv_unsigned_in_range 8 (nth i (b :: bs) (Z_to_bv 8 0))) as Hn. change (bv_modulus 8) with (2 ^ 8) in Hn.
apply (Z_testbit_high 8); lia.
Qed.
Lemma byte_of_word_le : forall (bs : list byte) i, (length bs <= 8)%nat -> (i < length bs)%nat ->
byte_of_word (Z_to_bv 64 (bytes_le_to_Z bs)) (Z.of_nat i) = nth i bs (Z_to_bv 8 0).
Proof.
intros bs i Hlen Hi. unfold byte_of_word.
pose proof (bytes_le_to_Z_bound bs) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
assert (Hlt : bytes_le_to_Z bs < 2 ^ 64).
{ eapply Z.lt_le_trans; [exact Hb|]. apply Z.pow_le_mono_r; lia. }
rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2 ^ 64). rewrite Z.mod_small by lia.
apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2 ^ 8).
apply shiftr_bytes_le_mod256. exact Hi.
Qed.
Lemma byte_of_word_low32 : forall (sg : bool) (w : word) i, 0 <= i < 4 ->
byte_of_word (if sg then sext 64 (bv_extract 0 32 w) else zext 64 (bv_extract 0 32 w)) i = byte_of_word w i.
Proof.
intros sg w i Hi. unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned.
change (bv_wrap 8 ?x) with (x mod 2 ^ 8).
pose proof (u64_range w) as Hw.
assert (Hlow : forall v : word, bv_unsigned v mod 2 ^ 32 = bv_unsigned w mod 2 ^ 32 ->
(Z.shiftr (bv_unsigned v) (8 * i)) mod 2 ^ 8 = (Z.shiftr (bv_unsigned w) (8 * i)) mod 2 ^ 8).
{ intros v Hv. pose proof (u64_range v). apply Z.bits_inj'. intros k Hk.
destruct (Z_lt_le_dec k 8) as [Hk8|Hk8].
- rewrite !Z.mod_pow2_bits_low, !Z.shiftr_spec by lia.
rewrite <- (Z.mod_pow2_bits_low (bv_unsigned v) 32) by lia.
rewrite <- (Z.mod_pow2_bits_low (bv_unsigned w) 32) by lia. rewrite Hv. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity. }
apply Hlow. destruct sg.
- unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed. rewrite bv_extract_unsigned, Z.shiftr_0_r.
unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
change (bv_half_modulus 32) with (2 ^ 31).
set (x := bv_unsigned w mod 2 ^ 32). pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)) as Hx.
fold x in Hx.
destruct (Z_lt_le_dec x (2 ^ 31)) as [Hs|Hs].
+ rewrite (Z.mod_small (x + 2^31) (2^32)) by lia. replace (x + 2 ^ 31 - 2 ^ 31) with x by lia.
rewrite (Z.mod_small x (2^64)) by lia. apply Z.mod_small. lia.
+ replace ((x + 2 ^ 31) mod 2 ^ 32) with (x + 2^31 - 2^32).
2:{ symmetry. rewrite <- (Z.mod_add (x + 2 ^ 31) (-1) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia. }
replace (x + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with (x - 2 ^ 32) by lia.
replace ((x - 2 ^ 32) mod 2 ^ 64) with (x - 2^32 + 2^64).
2:{ symmetry. rewrite <- (Z.mod_add (x - 2 ^ 32) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
replace (x - 2 ^ 32 + 2 ^ 64) with (x + (2^32 - 1) * 2 ^ 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
- unfold zext. rewrite bv_zero_extend_unsigned', bv_extract_unsigned, Z.shiftr_0_r.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)).
rewrite (Z.mod_small (_ mod 2 ^ 32) (2 ^ 64)) by lia. apply Z.mod_mod. lia.
Qed.
Lemma byte_of_data_word : forall E d s (n : N) i,
0 <= s -> (Z.to_nat s + N.to_nat n <= length (ed E d))%nat -> (N.to_nat n <= 8)%nat ->
(i < N.to_nat n)%nat ->
Some (byte_of_word (Z_to_bv 64 (data_word E d s n)) (Z.of_nat i)) = nth_error (ed E d) (Z.to_nat s + i).
Proof.
intros E d s n i Hs Hlen Hn Hi. unfold data_word.
set (bs := firstn (N.to_nat n) (skipn (Z.to_nat s) (ed E d))).
assert (Hl : length bs = N.to_nat n).
{ subst bs. rewrite length_firstn, length_skipn. lia. }
rewrite byte_of_word_le by lia.
rewrite <- (nth_error_nth' bs (Z_to_bv 8 0)) by lia. subst bs.
rewrite nth_error_firstn, nth_error_skipn. replace (i <? N.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
reflexivity.
Qed.
Definition canary_bytes (rb : list byte) : list byte :=
firstn 1 rb ++ [Z_to_bv 8 0] ++ firstn 6 (skipn 2 rb).
Definition canary_word (rb : list byte) : word := Z_to_bv 64 (bytes_le_to_Z (canary_bytes rb)).
Lemma length_canary_bytes : forall rb, (8 <= length rb)%nat -> length (canary_bytes rb) = 8%nat.
Proof.
intros rb H. unfold canary_bytes. rewrite !length_app, !length_firstn, length_skipn. cbn [length]. lia.
Qed.
Lemma canary_bytes_nth : forall rb i, (8 <= length rb)%nat -> (i < 8)%nat ->
nth_error (canary_bytes rb) i = if Nat.eqb i 1 then Some (Z_to_bv 8 0) else nth_error rb i.
Proof.
intros rb i Hlen Hi. unfold canary_bytes.
destruct i as [|[|i]].
- cbn [Nat.eqb]. rewrite nth_error_app1 by (rewrite length_firstn; lia). rewrite nth_error_firstn.
replace (0 <? 1)%nat with true by reflexivity. reflexivity.
- cbn [Nat.eqb]. rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
replace (1 - Nat.min 1 (length rb))%nat with 0%nat by lia. reflexivity.
- cbn [Nat.eqb]. rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
replace (S (S i) - Nat.min 1 (length rb))%nat with (S i) by lia. cbn [nth_error app].
rewrite nth_error_firstn, nth_error_skipn. replace (i <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
destruct rb as [|b0 [|b1 rb]]; cbn in Hlen; try lia. reflexivity.
Qed.
Lemma canary_word_byte : forall rb i, (8 <= length rb)%nat -> (i < 8)%nat ->
Some (byte_of_word (canary_word rb) (Z.of_nat i)) = if Nat.eqb i 1 then Some (Z_to_bv 8 0) else nth_error rb i.
Proof.
intros rb i Hlen Hi. unfold canary_word.
rewrite byte_of_word_le by (rewrite length_canary_bytes; lia).
rewrite <- canary_bytes_nth by lia. symmetry. apply nth_error_nth'. rewrite length_canary_bytes; lia.
Qed.
Section e.
Variable segs : list Segment.
Context {fx : FPState}.
Fixpoint add_chunk_sem (rs : smem) (b : option nat) (c : chunk) : option (smem * list chunk) :=
match rs with
| [] => None
| r :: rs' =>
if obase_eqb (r_base r) b && (r_lo r <=? c_off c) && (c_off c <? r_hi r)
then if chunk_inside r c
then Some (mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) (c :: r_chunks r) :: rs', r_chunks r)
else None
else match add_chunk_sem rs' b c with
| Some (rs'', cs) => Some (r :: rs'', cs)
| None => None
end
end.
Lemma obase_eqb_true : forall a b, obase_eqb a b = true -> a = b.
Proof.
intros [n|] [m|] H; cbn in H; try discriminate; [|reflexivity].
apply Nat.eqb_eq in H. subst. reflexivity.
Qed.
Definition add_chunk_region (r : region) (c : chunk) : region :=
mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) (c :: r_chunks r).
Lemma add_chunk_region_facts : forall E m r c,
chunk_inside r c = true -> region_wf r = true -> region_ok segs E m r ->
chunk_ok segs E m (base_val E (r_base r)) c ->
region_wf (add_chunk_region r c) = true /\ region_ok segs E m (add_chunk_region r c)
/\ extent_of (add_chunk_region r c) = extent_of r /\ skel (add_chunk_region r c) = skel r.
Proof.
intros E m r c Hci Hwf Hok Hc. destruct Hok as (H0 & H1 & Hw & Hcs).
split; [|split; [|split; reflexivity]].
- unfold region_wf in Hwf |- *; cbn [add_chunk_region r_lo r_hi r_wlo r_whi r_chunks forallb].
apply andb_prop in Hwf as [Hwf1 Hwf2]. rewrite Hwf1. cbn [andb].
apply andb_true_intro. split; [|exact Hwf2].
unfold chunk_inside in Hci |- *. cbn [r_lo r_hi]. exact Hci.
- unfold region_ok; cbn [add_chunk_region r_base r_lo r_hi r_wlo r_whi r_chunks].
split; [exact H0|]. split; [exact H1|]. split; [exact Hw|]. constructor; [exact Hc| exact Hcs].
Qed.
Lemma add_chunk_sem_facts : forall E m rs b c rs' cs,
add_chunk_sem rs b c = Some (rs', cs) ->
regions_wf rs = true -> Forall (region_ok segs E m) rs ->
(Forall (chunk_ok segs E m (base_val E b)) cs -> chunk_ok segs E m (base_val E b) c) ->
regions_wf rs' = true /\ Forall (region_ok segs E m) rs' /\ map extent_of rs' = map extent_of rs
/\ skeleton rs' = skeleton rs.
Proof.
intros E m rs b c. induction rs as [|r rs IH]; intros rs' cs H Hwf Hok Hc; cbn in H; [discriminate|].
cbn in Hwf. apply andb_prop in Hwf as [Hwfr Hwf]. inversion Hok as [|r0 rs0 Hokr Hokrs]; subst.
destruct (obase_eqb (r_base r) b && (r_lo r <=? c_off c) && (c_off c <? r_hi r)) eqn:Hsel.
- destruct (chunk_inside r c) eqn:Hci; [|discriminate]. injection H as <- <-.
apply andb_prop in Hsel as [Hsel _]. apply andb_prop in Hsel as [Hb _]. apply obase_eqb_true in Hb.
assert (Hc' : chunk_ok segs E m (base_val E (r_base r)) c).
{ rewrite Hb. apply Hc. rewrite <- Hb. destruct Hokr as (_ & _ & _ & Hcs). exact Hcs. }
destruct (add_chunk_region_facts E m r c Hci Hwfr Hokr Hc') as (W & O & X & SK).
change (mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) (c :: r_chunks r)) with (add_chunk_region r c).
cbn [regions_wf map]. unfold skeleton. cbn [map]. rewrite W, Hwf, X, SK.
repeat split; try reflexivity. constructor; assumption.
- destruct (add_chunk_sem rs b c) as [[rs'' cs']|] eqn:Hrs; [|discriminate]. injection H as <- <-.
destruct (IH rs'' cs' eq_refl Hwf Hokrs Hc) as (W & O & X & SK).
cbn [regions_wf map]. unfold skeleton in SK |- *. cbn [map]. rewrite Hwfr, W, X, SK.
repeat split; try reflexivity. constructor; assumption.
Qed.
Lemma mem_ok_add_chunk_sem : forall E m rs b c rs' cs,
mem_ok segs E m rs -> add_chunk_sem rs b c = Some (rs', cs) ->
(Forall (chunk_ok segs E m (base_val E b)) cs -> chunk_ok segs E m (base_val E b) c) ->
mem_ok segs E m rs'.
Proof.
intros E m rs b c rs' cs (Hwf & Hok & Hpd) H Hc.
destruct (add_chunk_sem_facts E m rs b c rs' cs H Hwf Hok Hc) as (W & O & X & _).
split; [exact W|]. split; [exact O|].
eapply pairwise_disjoint_extents; [symmetry; exact X| exact Hpd].
Qed.
Lemma st_ok_add_chunk_sem : forall E ss ms b c rs' cs,
st_ok segs E ss ms -> add_chunk_sem (ss_mem ss) b c = Some (rs', cs) ->
(Forall (chunk_ok segs E (ms_mem ms) (base_val E b)) cs -> chunk_ok segs E (ms_mem ms) (base_val E b) c) ->
st_ok segs E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) rs' (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms b c rs' cs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) H Hc.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
eapply mem_ok_add_chunk_sem; eauto.
Qed.
Lemma add_chunk_sem_skeleton : forall rs b c rs' cs,
add_chunk_sem rs b c = Some (rs', cs) -> skeleton rs' = skeleton rs.
Proof.
intros rs b c. induction rs as [|r rs IH]; intros rs' cs H; cbn in H; [discriminate|].
destruct (obase_eqb (r_base r) b && (r_lo r <=? c_off c) && (c_off c <? r_hi r)).
- destruct (chunk_inside r c); [|discriminate]. injection H as <- <-. reflexivity.
- destruct (add_chunk_sem rs b c) as [[rs'' cs']|] eqn:Hrs; [|discriminate]. injection H as <- <-.
cbn. unfold skeleton in IH. rewrite (IH rs'' cs' eq_refl). reflexivity.
Qed.
Definition add_chunk_ (b : option nat) (c : chunk) (ss : sstate) : sstate :=
match add_chunk_sem (ss_mem ss) b c with
| Some (rs', _) => mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) rs' (ss_resv ss) (ss_facts ss)
| None => ss
end.
Lemma chunk_ok_cval_byte : forall E m base off w v i,
chunk_ok segs E m base (mkChunk off (CVal w v)) -> 0 <= i < Z.of_N w ->
mbyte segs m (base + off + i) = Some (byte_of_word (sv_denot E v) i).
Proof.
intros E m base off w v i Hc Hi. destruct (Hc i) as (b & Hb1 & Hb2); [cbn; unfold c_len; cbn; lia|].
cbn [c_off c_val cbyte] in Hb1, Hb2. injection Hb1 as <-. exact Hb2.
Qed.
Lemma chunk_ok_cdata_byte : forall E m base off d s len i,
chunk_ok segs E m base (mkChunk off (CData d s len)) -> 0 <= i < len ->
exists b, nth_error (ed E d) (Z.to_nat (s + i)) = Some b /\ mbyte segs m (base + off + i) = Some b.
Proof.
intros E m base off d s len i Hc Hi. destruct (Hc i) as (b & Hb1 & Hb2); [cbn; unfold c_len; cbn; lia|].
cbn [c_off c_val cbyte] in Hb1, Hb2. exists b. split; assumption.
Qed.
Lemma chunk_ok_cdata_intro : forall E m base off d s len,
0 <= s ->
(forall i, 0 <= i < len -> exists b, nth_error (ed E d) (Z.to_nat (s + i)) = Some b /\
mbyte segs m (base + off + i) = Some b) ->
chunk_ok segs E m base (mkChunk off (CData d s len)).
Proof.
intros E m base off d s len Hs H i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *. apply H. exact Hi.
Qed.
Lemma chunk_ok_cval_intro : forall E m base off (w : N) v,
(forall i, 0 <= i < Z.of_N w -> mbyte segs m (base + off + i) = Some (byte_of_word (sv_denot E v) i)) ->
chunk_ok segs E m base (mkChunk off (CVal w v)).
Proof.
intros E m base off w v H i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
eexists. split; [reflexivity|]. apply H. exact Hi.
Qed.
Lemma chunk_ok_sext32_data : forall E m base off d s i,
chunk_ok segs E m base (mkChunk off (CVal 4 (SExt true 32 (SData d s 4)))) ->
0 <= s -> (Z.to_nat s + 4 <= length (ed E d))%nat -> 0 <= i < 4 ->
exists b, nth_error (ed E d) (Z.to_nat (s + i)) = Some b /\ mbyte segs m (base + off + i) = Some b.
Proof.
intros E m base off d s i Hc Hs Hlen Hi.
pose proof (chunk_ok_cval_byte E m base off 4 _ i Hc ltac:(cbn; lia)) as Hb.
cbn [sv_denot] in Hb. rewrite (byte_of_word_low32 true) in Hb by lia.
exists (byte_of_word (Z_to_bv 64 (data_word E d s 4)) i). split; [|exact Hb].
replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (byte_of_data_word E d s 4 (Z.to_nat i)) by (cbn; lia).
f_equal. lia.
Qed.
Lemma guard_data_chunk_ok : forall E m base G d,
(8 <= length (ed E d))%nat ->
chunk_ok segs E m base (mkChunk G (CVal 4 (SExt true 32 (SData d 0 4)))) ->
chunk_ok segs E m base (mkChunk (G + 4) (CVal 4 (SExt true 32 (SData d 4 4)))) ->
chunk_ok segs E m base (mkChunk G (CData d 0 8)).
Proof.
intros E m base G d Hlen C0 C4. apply chunk_ok_cdata_intro; [lia|]. intros i Hi.
destruct (Z_lt_le_dec i 4) as [Hl|Hl].
- apply (chunk_ok_sext32_data E m base G d 0 i C0); lia.
- replace (base + G + i) with (base + (G + 4) + (i - 4)) by lia. replace (0 + i) with (4 + (i - 4)) by lia.
apply (chunk_ok_sext32_data E m base (G + 4) d 4 (i - 4) C4); lia.
Qed.
Lemma canary_chunk_ok : forall E m base G d n,
(8 <= length (ed E d))%nat -> ew E n = canary_word (ed E d) ->
chunk_ok segs E m base (mkChunk G (CData d 0 1)) ->
chunk_ok segs E m base (mkChunk (G + 1) (CVal 1 (SLit 0))) ->
chunk_ok segs E m base (mkChunk (G + 2) (CData d 2 6)) ->
chunk_ok segs E m base (mkChunk G (CVal 8 (SOff n 0))).
Proof.
intros E m base G d n Hlen Hn C0 C1 C2. apply chunk_ok_cval_intro. intros i Hi.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Hn.
assert (exists k, i = Z.of_nat k /\ (k < 8)%nat) as (k & -> & Hk) by (exists (Z.to_nat i); lia).
pose proof (canary_word_byte (ed E d) k Hlen Hk) as HB.
destruct (Nat.eq_dec k 1) as [->|Hne1].
- cbn [Nat.eqb Z.of_nat Pos.of_succ_nat] in HB |- *. injection HB as HB.
assert (HB2 : byte_of_word (canary_word (ed E d)) (Z.of_nat 1) = Z_to_bv 8 0) by (apply bv_eq; exact HB).
rewrite HB2.
pose proof (chunk_ok_cval_byte E m base (G + 1) 1 (SLit 0) 0 C1 ltac:(cbn; lia)) as Hb.
replace (base + G + Z.of_nat 1) with (base + (G + 1) + 0) by lia. rewrite Hb. f_equal.
- replace (Nat.eqb k 1) with false in HB by (symmetry; apply Nat.eqb_neq; exact Hne1).
destruct (Nat.eq_dec k 0) as [->|Hne0].
+ destruct (chunk_ok_cdata_byte E m base G d 0 1 0 C0 ltac:(lia)) as (b & Hb1 & Hb2).
replace (Z.to_nat (0 + 0)) with 0%nat in Hb1 by reflexivity. change (Z.of_nat 0) with 0 in HB |- *.
rewrite Hb1 in HB.
assert (HB2 : byte_of_word (canary_word (ed E d)) 0 = b) by (injection HB as HB'; first [exact HB' | apply bv_eq; exact HB']).
rewrite HB2. exact Hb2.
+ destruct (chunk_ok_cdata_byte E m base (G + 2) d 2 6 (Z.of_nat k - 2) C2 ltac:(lia)) as (b & Hb1 & Hb2).
replace (Z.to_nat (2 + (Z.of_nat k - 2))) with k in Hb1 by lia. rewrite Hb1 in HB.
assert (HB2 : byte_of_word (canary_word (ed E d)) (Z.of_nat k) = b) by (injection HB as HB'; first [exact HB' | apply bv_eq; exact HB']).
rewrite HB2.
replace (base + (G + 2) + (Z.of_nat k - 2)) with (base + G + Z.of_nat k) in Hb2 by lia. exact Hb2.
Qed.
End e.
