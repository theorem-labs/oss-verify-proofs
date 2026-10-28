(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r
UI1w UI4l UI21 UI5o UI5l YI6b YL0g
UI3m UI5m UN0d
YI16 YI17 YI14 YI18 YI1a UI5c YI00 UI3u UI22 UI2u UI0l
YI5a UI23 YI0a YL00 YI05 UI5n UIZs.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI5f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition le16 (P : list Z) (k : nat) : Z := List.nth k P 0 + 256 * List.nth (k + 1)%nat P 0.
Definition le32 (P : list Z) (k : nat) : Z :=
List.nth k P 0 + 256 * List.nth (k + 1)%nat P 0 + 65536 * List.nth (k + 2)%nat P 0 + 16777216 * List.nth (k + 3)%nat P 0.
Definition lh_W (P : list Z) (n : Z) : Z := if 2 <=? n then le16 P 0 else 0.
Definition lh_H (P : list Z) (n : Z) : Z := if 4 <=? n then le16 P 2 else 0.
Definition lh_attr (P : list Z) (n : Z) : Z := if 8 <=? n then le32 P 4 else 0.
Definition lh_gen (P : list Z) (n : Z) : Z := if 12 <=? n then le32 P 8 else 0.
Definition lh_ngp (P : list Z) (n : Z) : Z := if 14 <=? n then le16 P 12 else 0.
Definition lh_r1 (n : Z) : Z := if 12 <=? n then 0 else 2 ^ 64 - 1.
Definition lh_r2 (n : Z) : Z := if 14 <=? n then 0 else 2 ^ 64 - 1.
Definition lh_cur (n : Z) : Z := Z.min 14 n.
Definition hd_rv (b : bool) : Z := if b then 0 else 2 ^ 64 - 1.
Lemma hd_lor_rv : forall b1 b2, Z.lor (hd_rv b1) (hd_rv b2) = hd_rv (b1 && b2).
Proof using. intros [|] [|]; reflexivity. Qed.
Fixpoint hd_cb (P : list Z) (n : Z) (t : list (Z * Z * Z)) (j : Z) : Z :=
match t with
| [] => 0
| (fo, k, s) :: t' =>
if (fo <=? j) && (j <? fo + k) then (if s + k <=? n then List.nth (Z.to_nat (s + j - fo)) P 0 else 0) else hd_cb P n t' j
end.
Definition hd_cf (m : word -> option byte) (a : Z) (P : list Z) (n : Z) (t : list (Z * Z * Z)) : Prop :=
forall j, 0 <= j < 48 -> mbyte ubs0segs m (a + j) = Some (Z_to_bv 8 (hd_cb P n t j)).
Definition hd_t5 : list (Z * Z * Z) := [(28, 2, 12); (20, 4, 8); (16, 4, 4); (26, 2, 2); (24, 2, 0)].
Lemma hd_cf_step : forall (m0 m2 : word -> option byte) a P n t fo k s,
hd_cf m0 a P n t ->
(forall j, 0 <= j < 48 -> ~ (fo <= j < fo + k) -> mbyte ubs0segs m2 (a + j) = mbyte ubs0segs m0 (a + j)) ->
(forall q, 0 <= q < k -> mbyte ubs0segs m2 (a + fo + q) = Some (Z_to_bv 8 (if s + k <=? n then List.nth (Z.to_nat (s + q)) P 0 else 0))) ->
hd_cf m2 a P n ((fo, k, s) :: t).
Proof using.
intros m0 m2 a P n t fo k s H0 Hout Hin j Hj. cbn [hd_cb].
destruct ((fo <=? j) && (j <? fo + k)) eqn:Ej.
- apply andb_true_iff in Ej. destruct Ej as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
replace (a + j) with (a + fo + (j - fo)) by lia. rewrite (Hin (j - fo)) by lia.
replace (s + (j - fo)) with (s + j - fo) by lia. reflexivity.
- rewrite (Hout j Hj); [apply H0; exact Hj|].
intros [E1 E2]. apply andb_false_iff in Ej. destruct Ej as [Ej|Ej]; [apply Z.leb_gt in Ej | apply Z.ltb_ge in Ej]; lia.
Qed.
Lemma hd_kb : forall lo1 hi1 lo2 hi2 (m m0 : word -> option byte) a,
kept2 lo1 hi1 lo2 hi2 m m0 -> 0 <= a < 2 ^ 64 -> ~ (lo1 <= a < hi1) -> ~ (lo2 <= a < hi2) ->
mbyte ubs0segs m a = mbyte ubs0segs m0 a.
Proof using.
intros lo1 hi1 lo2 hi2 m m0 a H Ha H1 H2. unfold mbyte.
rewrite (H (Z_to_bv 64 a)); [reflexivity | rewrite unsigned_lit_small by lia; exact H1 | rewrite unsigned_lit_small by lia; exact H2].
Qed.
Lemma hd_seg : forall (m m' : word -> option byte) sp0 lo1 hi1 p n P t,
kept2 lo1 hi1 (sp0 - 32) sp0 m' m -> sp0 - 176 <= lo1 -> hi1 <= sp0 - 80 -> 0 <= sp0 - 176 -> sp0 < 2 ^ 64 ->
0 <= p -> (0 < n -> p + n <= sp0 - 176) -> Z.of_nat (length P) = n ->
hd_cf m (sp0 - 80) P n t -> garr8 ubs0segs m p P ->
hd_cf m' (sp0 - 80) P n t /\ garr8 ubs0segs m' p P.
Proof using.
intros m m' sp0 lo1 hi1 p n P t HK Hl1 Hh1 Hs0 Hs1 Hp Hpn HL HC HG. split.
- intros j Hj. rewrite (hd_kb _ _ _ _ m' m (sp0 - 80 + j) HK) by lia. apply HC. exact Hj.
- apply (garr8_frame ubs0segs m m' p P HG). intros a Ha. apply (hd_kb _ _ _ _ m' m a HK); lia.
Qed.
Lemma hd_pl_kept : forall (m m' : word -> option byte) sp0 lo1 hi1 p n P,
kept2 lo1 hi1 (sp0 - 32) sp0 m' m -> sp0 - 176 <= lo1 -> 0 <= sp0 - 176 -> sp0 < 2 ^ 64 ->
0 <= p -> (0 < n -> p + n <= sp0 - 176) -> Z.of_nat (length P) = n ->
garr8 ubs0segs m p P -> garr8 ubs0segs m' p P.
Proof using.
intros m m' sp0 lo1 hi1 p n P HK Hl1 Hs0 Hs1 Hp Hpn HL HG.
apply (garr8_frame ubs0segs m m' p P HG). intros a Ha. apply (hd_kb _ _ _ _ m' m a HK); lia.
Qed.
Lemma hd_seg_cur : forall (m m' : word -> option byte) sp0 c,
kept2 (sp0 - 136) (sp0 - 120) (sp0 - 32) sp0 m' m -> 0 <= sp0 - 136 -> sp0 < 2 ^ 64 ->
word_mem ubs0segs m (sp0 - 120) c -> word_mem ubs0segs m' (sp0 - 120) c.
Proof using.
intros m m' sp0 c HK H0 H1 W k Hk. rewrite (hd_kb _ _ _ _ m' m (sp0 - 120 + Z.of_nat k) HK) by lia. apply W. exact Hk.
Qed.
Lemma hd_wm_rd : forall (m m' : word -> option byte) spc d k st a v,
(forall x : word, ~ (spc - RD_FRAME <= bv_unsigned x < spc) -> ~ (d <= bv_unsigned x < d + k) ->
~ (st + 16 <= bv_unsigned x < st + 24) -> m' x = m x) ->
0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= spc - RD_FRAME \/ spc <= a) -> (a + 8 <= d \/ d + k <= a) ->
(a + 8 <= st + 16 \/ st + 24 <= a) ->
word_mem ubs0segs m a v -> word_mem ubs0segs m' a v.
Proof using.
intros m m' spc d k st a v Hout H0 H1 D1 D2 D3 W kk Hk. rewrite <- (W kk Hk). unfold mbyte.
rewrite (Hout (Z_to_bv 64 (a + Z.of_nat kk))); [reflexivity | rewrite unsigned_lit_small by lia; lia ..].
Qed.
Lemma hd_kept_out : forall E (mem mem' : word -> option byte) r d n,
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> mem' x = mem x) -> mem_grows mem mem' ->
0 <= base_val E (r_base r) + r_lo r -> base_val E (r_base r) + r_hi r <= 2 ^ 64 ->
(base_val E (r_base r) + r_hi r <= d \/ d + n <= base_val E (r_base r) + r_lo r) ->
r_lo r <= r_wlo r -> r_whi r <= r_hi r -> region_kept ubs0segs E mem mem' r.
Proof using.
intros E mem mem' r d n Hout Hgr Hlo Hhi H1 Hw1 Hw2. split; intros a Ha.
- unfold mbyte. rewrite (Hout (Z_to_bv 64 a)); [reflexivity | rewrite unsigned_lit_small by lia; lia].
- apply (writable_at_grows ubs0segs mem mem'); assumption.
Qed.
Lemma hd_rd_post : forall (m1 m2 : word -> option byte) (regs2 : bvmap 5 word) (sp0 p n s k fo : Z) (P : list Z) t,
Z.of_nat (length P) = n -> 0 <= s -> 0 < k -> 0 <= fo -> fo + k <= 48 ->
0 <= sp0 - 176 -> sp0 < 2 ^ 64 -> 0 <= p -> (0 < n -> p + n <= sp0 - 176) ->
garr8 ubs0segs m1 p P -> hd_cf m1 (sp0 - 80) P n t ->
(forall q, 0 <= q < k -> hd_cb P n t (fo + q) = 0) ->
(forall x : word, ~ (sp0 - 144 - RD_FRAME <= bv_unsigned x < sp0 - 144) -> ~ (sp0 - 80 + fo <= bv_unsigned x < sp0 - 80 + fo + k) ->
~ (sp0 - 136 + 16 <= bv_unsigned x < sp0 - 136 + 24) -> m2 x = m1 x) ->
((Z.min s n + k <= n /\ getr regs2 10 = Z_to_bv 64 0 /\ word_mem ubs0segs m2 (sp0 - 136 + 16) (Z.min s n + k) /\
(forall i, 0 <= i < k -> mbyte ubs0segs m2 (sp0 - 80 + fo + i) = mbyte ubs0segs m1 (p + Z.min s n + i))) \/
(n < Z.min s n + k /\ getr regs2 10 = Z_to_bv 64 (2 ^ 64 - 1) /\ word_mem ubs0segs m2 (sp0 - 136 + 16) n /\
(forall i, 0 <= i < k -> mbyte ubs0segs m2 (sp0 - 80 + fo + i) = mbyte ubs0segs m1 (sp0 - 80 + fo + i)))) ->
getr regs2 10 = Z_to_bv 64 (hd_rv (s + k <=? n)) /\ word_mem ubs0segs m2 (sp0 - 120) (Z.min (s + k) n) /\
hd_cf m2 (sp0 - 80) P n ((fo, k, s) :: t) /\ garr8 ubs0segs m2 p P.
Proof using.
intros m1 m2 regs2 sp0 p n s k fo P t HL Hs Hk Hf0 Hf1 Hsp0 Hsp1 Hp Hpn HG HC HZ Hout Hrd.
assert (HRD : RD_FRAME = 32) by reflexivity.
assert (Hmb : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 176 <= a < sp0 - 144) -> ~ (sp0 - 80 + fo <= a < sp0 - 80 + fo + k) ->
~ (sp0 - 120 <= a < sp0 - 112) -> mbyte ubs0segs m2 a = mbyte ubs0segs m1 a).
{ intros a Ha H1 H2 H3. unfold mbyte. rewrite (Hout (Z_to_bv 64 a)); [reflexivity | rewrite unsigned_lit_small by lia; lia ..]. }
assert (HG2 : garr8 ubs0segs m2 p P).
{ apply (garr8_frame ubs0segs m1 m2 p P HG). intros a Ha. apply Hmb; lia. }
assert (Hout2 : forall j, 0 <= j < 48 -> ~ (fo <= j < fo + k) -> mbyte ubs0segs m2 (sp0 - 80 + j) = mbyte ubs0segs m1 (sp0 - 80 + j)).
{ intros j Hj Hn. apply Hmb; lia. }
unfold hd_rv.
destruct Hrd as [(Hok & R10 & Wc & Hby) | (Hfl & R10 & Wc & Hby)].
- assert (Hsn : s <= n) by (destruct (Z.min_spec s n) as [[_ E]|[_ E]]; lia).
rewrite Z.min_l in Hok, Wc, Hby by lia.
assert (Hc : (s + k <=? n) = true) by (apply Z.leb_le; lia). rewrite Hc.
split; [exact R10|]. split; [rewrite Z.min_l by lia; replace (sp0 - 120) with (sp0 - 136 + 16) by lia; exact Wc|].
split; [|exact HG2].
apply (hd_cf_step m1 m2 (sp0 - 80) P n t fo k s HC Hout2).
intros q Hq. rewrite Hc. rewrite (Hby q Hq).
replace (p + s + q) with (p + Z.of_nat (Z.to_nat (s + q))) by lia.
apply garr8_mbyte; [exact HG | lia].
- assert (Hc : (s + k <=? n) = false) by (apply Z.leb_gt; destruct (Z.min_spec s n) as [[_ E]|[_ E]]; lia). rewrite Hc.
split; [exact R10|]. split; [rewrite Z.min_r by lia; replace (sp0 - 120) with (sp0 - 136 + 16) by lia; exact Wc|].
split; [|exact HG2].
apply (hd_cf_step m1 m2 (sp0 - 80) P n t fo k s HC Hout2).
intros q Hq. rewrite Hc. rewrite (Hby q Hq).
replace (sp0 - 80 + fo + q) with (sp0 - 80 + (fo + q)) by lia. rewrite (HC (fo + q)) by lia. rewrite (HZ q Hq). reflexivity.
Qed.
Lemma hd_nth_b : forall P, bytes_ok P -> forall j, 0 <= List.nth j P 0 < 256.
Proof using.
intros P HB j. destruct (Nat.lt_ge_cases j (length P)) as [Hj|Hj].
- unfold bytes_ok in HB. rewrite Forall_forall in HB. apply HB. apply nth_In. exact Hj.
- rewrite nth_overflow by exact Hj. lia.
Qed.
Lemma hd_lb0 : forall w k, le_byte 0 w k = 0.
Proof using. intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma hd_lbyte : forall v (w k : nat) ek h b r, ek = 2 ^ (8 * Z.of_nat k) -> 0 <= v < 2 ^ (8 * Z.of_nat w) ->
v = ek * (256 * h + b) + r -> 0 <= b < 256 -> 0 <= r < ek -> 0 <= h -> le_byte v w k = b.
Proof using.
intros v w k ek h b r Hek Hv E Hb Hr Hh. unfold le_byte. rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat w))) by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite <- Hek.
rewrite <- (Z.div_unique v ek (256 * h + b) r) by first [left; lia | exact E].
replace (256 * h + b) with (b + h * 256) by ring. rewrite (Z.mod_add b h 256) by lia. apply Z.mod_small. exact Hb.
Qed.
Lemma hd_l16 : forall P s, bytes_ok P -> forall q, (q < 2)%nat -> le_byte (le16 P s) 2 q = List.nth (s + q) P 0.
Proof using.
intros P s HB q Hq. unfold le16. pose proof (hd_nth_b P HB s) as B0. pose proof (hd_nth_b P HB (s + 1)) as B1.
destruct q as [|[|q]]; [rewrite Nat.add_0_r | | lia].
- apply (hd_lbyte _ 2 0 1 (List.nth (s + 1) P 0) (List.nth s P 0) 0); [reflexivity | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | lia ..].
- apply (hd_lbyte _ 2 1 256 0 (List.nth (s + 1) P 0) (List.nth s P 0)); [reflexivity | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | lia ..].
Qed.
Lemma hd_l32 : forall P s, bytes_ok P -> forall q, (q < 4)%nat -> le_byte (le32 P s) 4 q = List.nth (s + q) P 0.
Proof using.
intros P s HB q Hq. unfold le32. pose proof (hd_nth_b P HB s) as B0. pose proof (hd_nth_b P HB (s + 1)) as B1.
pose proof (hd_nth_b P HB (s + 2)) as B2. pose proof (hd_nth_b P HB (s + 3)) as B3.
destruct q as [|[|[|[|q]]]]; [rewrite Nat.add_0_r | | | | lia].
- apply (hd_lbyte _ 4 0 1 (List.nth (s + 1) P 0 + 256 * List.nth (s + 2) P 0 + 65536 * List.nth (s + 3) P 0) (List.nth s P 0) 0);
[reflexivity | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | lia ..].
- apply (hd_lbyte _ 4 1 256 (List.nth (s + 2) P 0 + 256 * List.nth (s + 3) P 0) (List.nth (s + 1) P 0) (List.nth s P 0));
[reflexivity | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | lia ..].
- apply (hd_lbyte _ 4 2 65536 (List.nth (s + 3) P 0) (List.nth (s + 2) P 0) (List.nth s P 0 + 256 * List.nth (s + 1) P 0));
[reflexivity | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | lia ..].
- apply (hd_lbyte _ 4 3 16777216 0 (List.nth (s + 3) P 0) (List.nth s P 0 + 256 * List.nth (s + 1) P 0 + 65536 * List.nth (s + 2) P 0));
[reflexivity | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | lia ..].
Qed.
Lemma hd_dfld : forall m a P n fo (k : nat) s (s' : nat) g V,
hd_cf m a P n hd_t5 -> 0 <= fo -> fo + Z.of_nat k <= 48 ->
(forall q, (q < k)%nat -> hd_cb P n hd_t5 (fo + Z.of_nat q) = if g <=? n then List.nth (Z.to_nat (s + Z.of_nat q)) P 0 else 0) ->
(forall q, (q < k)%nat -> (g <=? n) = true -> le_byte V k q = List.nth (s' + q) P 0) ->
((g <=? n) = false -> V = 0) -> Z.of_nat s' = s ->
val_mem ubs0segs m (a + fo) k V.
Proof using.
intros m a P n fo k s s' g V HC H0 H1 HE HB HZ Hs q Hq. rewrite <- Z.add_assoc, HC by lia. rewrite (HE q Hq).
destruct (g <=? n) eqn:Hg.
- rewrite (HB q Hq eq_refl). do 3 f_equal. lia.
- rewrite (HZ eq_refl), hd_lb0. reflexivity.
Qed.
Lemma hd_zfld : forall m a P n fo (k : nat),
hd_cf m a P n hd_t5 -> 0 <= fo -> fo + Z.of_nat k <= 48 ->
(forall q, (q < k)%nat -> hd_cb P n hd_t5 (fo + Z.of_nat q) = 0) ->
val_mem ubs0segs m (a + fo) k 0.
Proof using.
intros m a P n fo k HC H0 H1 HE q Hq. rewrite <- Z.add_assoc, HC by lia. rewrite (HE q Hq), hd_lb0. reflexivity.
Qed.
Lemma hd_r16 : forall P s, bytes_ok P -> 0 <= le16 P s < 65536.
Proof using. intros P s HB. unfold le16. pose proof (hd_nth_b P HB s). pose proof (hd_nth_b P HB (s + 1)). lia. Qed.
Lemma hd_r32 : forall P s, bytes_ok P -> 0 <= le32 P s < 4294967296.
Proof using.
intros P s HB. unfold le32. pose proof (hd_nth_b P HB s). pose proof (hd_nth_b P HB (s + 1)).
pose proof (hd_nth_b P HB (s + 2)). pose proof (hd_nth_b P HB (s + 3)). lia.
Qed.
Lemma hd_obj : forall m a P n, bytes_ok P -> hd_cf m a P n hd_t5 ->
obj_at ubs0segs m a LAY_Config [0; 0; lh_attr P n; lh_gen P n; lh_W P n; lh_H P n; lh_ngp P n; 0; 0; 0].
Proof using.
intros m a P n HB HC.
pose proof (hd_r16 P 0 HB) as R0. pose proof (hd_r16 P 2 HB) as R2. pose proof (hd_r32 P 4 HB) as R4.
pose proof (hd_r32 P 8 HB) as R8. pose proof (hd_r16 P 12 HB) as R12.
cbn [obj_at LAY_Config]. unfold field_ok. cbn [fst snd].
change (N.to_nat 8) with 8%nat. change (N.to_nat 4) with 4%nat. change (N.to_nat 2) with 2%nat.
change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616. change (2 ^ (8 * Z.of_N 4)) with 4294967296.
change (2 ^ (8 * Z.of_N 2)) with 65536.
split; [split; [apply (hd_zfld m a P n 0 8 HC); [lia | cbn; lia | intros q Hq; do 8 (destruct q as [|q]; [reflexivity|]); lia] | lia]|].
split; [split; [apply (hd_zfld m a P n 8 8 HC); [lia | cbn; lia | intros q Hq; do 8 (destruct q as [|q]; [reflexivity|]); lia] | lia]|].
split; [split; [apply (hd_dfld m a P n 16 4 4 4 8 _ HC); [lia | cbn; lia | intros q Hq; do 4 (destruct q as [|q]; [reflexivity|]); lia
| intros q Hq Hg; unfold lh_attr; rewrite Hg; apply hd_l32; [exact HB | exact Hq] | intros Hg; unfold lh_attr; rewrite Hg; reflexivity | reflexivity]
| unfold lh_attr; destruct (8 <=? n); lia]|].
split; [split; [apply (hd_dfld m a P n 20 4 8 8 12 _ HC); [lia | cbn; lia | intros q Hq; do 4 (destruct q as [|q]; [reflexivity|]); lia
| intros q Hq Hg; unfold lh_gen; rewrite Hg; apply hd_l32; [exact HB | exact Hq] | intros Hg; unfold lh_gen; rewrite Hg; reflexivity | reflexivity]
| unfold lh_gen; destruct (12 <=? n); lia]|].
split; [split; [apply (hd_dfld m a P n 24 2 0 0 2 _ HC); [lia | cbn; lia | intros q Hq; do 2 (destruct q as [|q]; [reflexivity|]); lia
| intros q Hq Hg; unfold lh_W; rewrite Hg; apply hd_l16; [exact HB | exact Hq] | intros Hg; unfold lh_W; rewrite Hg; reflexivity | reflexivity]
| unfold lh_W; destruct (2 <=? n); lia]|].
split; [split; [apply (hd_dfld m a P n 26 2 2 2 4 _ HC); [lia | cbn; lia | intros q Hq; do 2 (destruct q as [|q]; [reflexivity|]); lia
| intros q Hq Hg; unfold lh_H; rewrite Hg; apply hd_l16; [exact HB | exact Hq] | intros Hg; unfold lh_H; rewrite Hg; reflexivity | reflexivity]
| unfold lh_H; destruct (4 <=? n); lia]|].
split; [split; [apply (hd_dfld m a P n 28 2 12 12 14 _ HC); [lia | cbn; lia | intros q Hq; do 2 (destruct q as [|q]; [reflexivity|]); lia
| intros q Hq Hg; unfold lh_ngp; rewrite Hg; apply hd_l16; [exact HB | exact Hq] | intros Hg; unfold lh_ngp; rewrite Hg; reflexivity | reflexivity]
| unfold lh_ngp; destruct (14 <=? n); lia]|].
split; [split; [apply (hd_zfld m a P n 30 2 HC); [lia | cbn; lia | intros q Hq; do 2 (destruct q as [|q]; [reflexivity|]); lia] | lia]|].
split; [split; [apply (hd_zfld m a P n 32 8 HC); [lia | cbn; lia | intros q Hq; do 8 (destruct q as [|q]; [reflexivity|]); lia] | lia]|].
split; [split; [apply (hd_zfld m a P n 40 8 HC); [lia | cbn; lia | intros q Hq; do 8 (destruct q as [|q]; [reflexivity|]); lia] | lia]|].
exact I.
Qed.
Lemma hd_hdr : forall P n, Z.of_nat (length P) = n -> lh_r1 n = 0 -> lh_r2 n = 0 -> lh_cur n = 14 /\
hdr5 P = (false, (lh_W P n, lh_H P n, lh_attr P n, lh_gen P n, lh_ngp P n), skipn 14 P).
Proof using.
intros P n HL H1 H2. unfold lh_r2 in H2. destruct (Z.leb_spec 14 n) as [Hn|Hn]; [|vm_compute in H2; discriminate H2].
split; [unfold lh_cur; lia|].
unfold lh_W, lh_H, lh_attr, lh_gen, lh_ngp.
rewrite (proj2 (Z.leb_le 2 n)), (proj2 (Z.leb_le 4 n)), (proj2 (Z.leb_le 8 n)), (proj2 (Z.leb_le 12 n)), (proj2 (Z.leb_le 14 n)) by lia.
rewrite YO08.hdr5_ok by lia.
do 14 (destruct P as [|? P]; [cbn in HL; lia|]). cbn [firstn skipn]. rewrite !YO08.le_bytes_2, !YO08.le_bytes_4.
unfold le16, le32. cbn [List.nth Nat.add]. reflexivity.
Qed.
Definition L_HD1 : Z := Eval vm_compute in (ubs0_A_LLVMFuzzerTestOneInput + 0x30).
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Definition hd_mid (regs : bvmap 5 word) L A mem md (p n : Z) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
journal ubs0_msyms MR LIB_STACK (spZ regs) [] L A mem md L A mem2 md /\ mem_grows mem mem2 /\
(forall x : word, ~ (spZ regs - 144 <= bv_unsigned x < spZ regs) -> mem2 x = mem x) /\
saved_ok mem2 (spZ regs) regs /\
word_mem ubs0segs mem2 (spZ regs - 136) p /\ word_mem ubs0segs mem2 (spZ regs - 128) n /\
word_mem ubs0segs mem2 (spZ regs - 120) 0 /\
(forall j, 0 <= j < 48 -> mbyte ubs0segs mem2 (spZ regs - 80 + j) = Some (Z_to_bv 8 0)) /\
getr regs2 2 = Z_to_bv 64 (spZ regs - 144) /\ untouched_ok regs regs2.
Lemma hd_pro : forall (regs : bvmap 5 word) L A mem md (p n : Z) (Q : config -> Prop),
fn_pre ubs0_msyms MR LIB_STACK L A regs mem md ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
(forall (regs2 : bvmap 5 word) (mem2 : word -> option byte), hd_mid regs L A mem md p n regs2 mem2 ->
SR ubs0segs (mkCfg (mkst regs2 (Z_to_bv 64 L_HD1) mem2 (seg_rom ubs0segs)) md) Q) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom ubs0segs)) md) Q.
Proof using IMG LAWS.
intros regs L A mem md p n Q HPRE G10 G11 Hp Hn K.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK = 16384) by reflexivity.
pose proof HPRE as (HH & Hra & (Hal16 & HSTK0 & Hceil & H63 & Hstw) & Htp & Herr).
pose proof (journal_init ubs0_msyms MR LIB_STACK [] L A regs mem md HPRE) as HJ.
set (sp := spZ regs) in *.
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok ubs0segs E
(mkSS LLVM sr_atoms
[ YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [] ;
YP09.mkRegion (Some 2%nat) (-136) (-120) (-136) (-120) [] ;
YP09.mkRegion (Some 2%nat) (-120) (-112) (-120) (-112) [] ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK) (2^63) 4) ] [] []))
(mkst regs (Z_to_bv 64 LLVM) mem (seg_rom ubs0segs))).
{ subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack ubs0segs _ mem 2 sp); [exact HE2 | lia | lia | intros a Ha; apply Hstw; lia].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|]. apply Forall_nil.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|]. apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2. repeat split; lia.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2. change (2 ^ 4) with 16. repeat split; lia. }
change mem with (ms_mem (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom ubs0segs))) in HJ at 2.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_memset.
{ wr_norm. eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG. rename HF into HF0, HG into HG0.
assert (W1 : word_mem ubs0segs (ms_mem ms) (sp + -8) (bv_unsigned (getr regs 1)))
by (eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-8) (SOff 1 0) sp _ HS);
[ reflexivity | reflexivity | solve [cbv; auto 12] | exact HE2
| cbn [sv_denot]; rewrite Z.add_0_r, (HE 1%nat 1%bv eq_refl); reflexivity | apply bv_unsigned_in_range ]).
assert (W8 : word_mem ubs0segs (ms_mem ms) (sp + -16) (bv_unsigned (getr regs 8)))
by (eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-16) (SOff 8 0) sp _ HS);
[ reflexivity | reflexivity | solve [cbv; auto 12] | exact HE2
| cbn [sv_denot]; rewrite Z.add_0_r, (HE 8%nat 8%bv eq_refl); reflexivity | apply bv_unsigned_in_range ]).
assert (W9 : word_mem ubs0segs (ms_mem ms) (sp + -24) (bv_unsigned (getr regs 9)))
by (eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-24) (SOff 9 0) sp _ HS);
[ reflexivity | reflexivity | solve [cbv; auto 12] | exact HE2
| cbn [sv_denot]; rewrite Z.add_0_r, (HE 9%nat 9%bv eq_refl); reflexivity | apply bv_unsigned_in_range ]).
assert (W18 : word_mem ubs0segs (ms_mem ms) (sp + -32) (bv_unsigned (getr regs 18)))
by (eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-32) (SOff 18 0) sp _ HS);
[ reflexivity | reflexivity | solve [cbv; auto 12] | exact HE2
| cbn [sv_denot]; rewrite Z.add_0_r, (HE 18%nat 18%bv eq_refl); reflexivity | apply bv_unsigned_in_range ]).
assert (Wp : word_mem ubs0segs (ms_mem ms) (sp + -136) p)
by (eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-136) (SOff 10 0) sp _ HS);
[ reflexivity | reflexivity | solve [cbv; auto 12] | exact HE2
| cbn [sv_denot]; rewrite Z.add_0_r, (HE 10%nat 10%bv eq_refl), G10, Z_to_bv_bv_unsigned; reflexivity | lia ]).
assert (Wn : word_mem ubs0segs (ms_mem ms) (sp + -128) n)
by (eapply (st_chunk_word _ _ _ 1%nat _ 2%nat (-128) (SOff 11 0) sp _ HS);
[ reflexivity | reflexivity | solve [cbv; auto 12] | exact HE2
| cbn [sv_denot]; rewrite Z.add_0_r, (HE 11%nat 11%bv eq_refl), G11, Z_to_bv_bv_unsigned; reflexivity | lia ]).
assert (Wc : word_mem ubs0segs (ms_mem ms) (sp + -120) 0)
by (eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-120) (SLit 0) sp _ HS);
[ reflexivity | reflexivity | solve [cbv; auto 12] | exact HE2 | reflexivity | lia ]).
jreg HS (2%bv:reg) as J2. rewrite HE2 in J2.
jreg HS (3%bv:reg) as J3. rewrite (HE 3%nat 3%bv eq_refl) in J3.
jreg HS (4%bv:reg) as J4. rewrite (HE 4%nat 4%bv eq_refl) in J4.
jreg HS (19%bv:reg) as J19. rewrite (HE 19%nat 19%bv eq_refl) in J19.
jreg HS (20%bv:reg) as J20. rewrite (HE 20%nat 20%bv eq_refl) in J20.
jreg HS (21%bv:reg) as J21. rewrite (HE 21%nat 21%bv eq_refl) in J21.
jreg HS (22%bv:reg) as J22. rewrite (HE 22%nat 22%bv eq_refl) in J22.
jreg HS (23%bv:reg) as J23. rewrite (HE 23%nat 23%bv eq_refl) in J23.
jreg HS (24%bv:reg) as J24. rewrite (HE 24%nat 24%bv eq_refl) in J24.
jreg HS (25%bv:reg) as J25. rewrite (HE 25%nat 25%bv eq_refl) in J25.
jreg HS (26%bv:reg) as J26. rewrite (HE 26%nat 26%bv eq_refl) in J26.
jreg HS (27%bv:reg) as J27. rewrite (HE 27%nat 27%bv eq_refl) in J27.
jreg HS (10%bv:reg) as M10. rewrite HE2 in M10. replace (sp + -80) with (sp - 80) in M10 by lia.
jreg HS (11%bv:reg) as M11. jreg HS (12%bv:reg) as M12. jreg HS (1%bv:reg) as M1.
eapply SR_bind.
{ eapply (jmemset ubs0_msyms MR LAWS IMG ubs0_A_memset ubs0_memset_spec _ _ _ LIB_STACK _ _ _ _ _ _ _ _ _ (sp - 80) 0 48).
- exact HS. - reflexivity. - reflexivity. - exact HJ.
- exact M10. - exact M11. - exact M12. - exact M1.
- apply ret_ok_even; vm_compute; reflexivity.
- lia. - lia. - lia. - lia.
- intros i Hi. apply UN0d.writable_off_img_present; [lia | unfold UN0d.in_img1; lia |].
apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
- intros a Ha. unfold wr_byte. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hm10 & Hregs2 & Hout2 & Hgr2 & Hz2).
assert (Hmk : forall a, 0 <= a < 2 ^ 64 -> (a < sp - 80 \/ sp - 32 <= a) -> mbyte ubs0segs mem2 a = mbyte ubs0segs (ms_mem ms) a).
{ intros a Ha Hx. unfold mbyte. rewrite (Hout2 (Z_to_bv 64 a)); [reflexivity | rewrite unsigned_lit_small by lia; lia]. }
assert (WK : forall a v, word_mem ubs0segs (ms_mem ms) a v -> 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= sp - 80 \/ sp - 32 <= a) ->
word_mem ubs0segs mem2 a v).
{ intros a v W H0 H1 H2 k Hk. rewrite Hmk by lia. apply W. exact Hk. }
apply (K regs2 mem2). unfold hd_mid. change (spZ regs) with sp.
split; [exact HJ2|].
split; [exact (mem_grows_trans _ _ _ HG0 Hgr2)|].
split.
{ intros x Hx. rewrite (Hout2 x) by lia. apply HF0. intros (r & Hr & Hw). cbv [In] in Hr.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [r_base r_wlo r_whi base_val] in Hw; rewrite HE2 in Hw; lia. }
split.
{ unfold saved_ok. change (spZ regs) with sp.
split; [apply WK; [replace (sp - 8) with (sp + -8) by lia; exact W1 | lia | lia | lia]|].
split; [apply WK; [replace (sp - 16) with (sp + -16) by lia; exact W8 | lia | lia | lia]|].
split; [apply WK; [replace (sp - 24) with (sp + -24) by lia; exact W9 | lia | lia | lia]|].
apply WK; [replace (sp - 32) with (sp + -32) by lia; exact W18 | lia | lia | lia]. }
split; [apply WK; [replace (sp - 136) with (sp + -136) by lia; exact Wp | lia | lia | lia]|].
split; [apply WK; [replace (sp - 128) with (sp + -128) by lia; exact Wn | lia | lia | lia]|].
split; [apply WK; [replace (sp - 120) with (sp + -120) by lia; exact Wc | lia | lia | lia]|].
split; [exact Hz2|].
split; [rewrite Hregs2 by (vm_compute; reflexivity); rewrite J2; f_equal; lia|].
unfold untouched_ok.
repeat split; (rewrite Hregs2; [|vm_compute; reflexivity]); assumption.
Qed.
Lemma hd_ss : forall pc (regs : bvmap 5 word) (mem : word -> option byte),
st_ok ubs0segs (Ereg regs []) (mkSS pc sr_atoms [] None (mkFacts [] [] [])) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs0segs)).
Proof using.
intros pc regs mem. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.
Definition hd_inv (regs0 : bvmap 5 word) (m : word -> option byte) (sp0 p n : Z) (D : list Z) (t : list (Z * Z * Z)) (c : Z) : Prop :=
saved_ok m sp0 regs0 /\ word_mem ubs0segs m (sp0 - 136) p /\ word_mem ubs0segs m (sp0 - 128) n /\
word_mem ubs0segs m (sp0 - 120) c /\ hd_cf m (sp0 - 80) D n t /\ garr8 ubs0segs m p D.
Lemma hd_inv_eq : forall regs0 (m m' : word -> option byte) sp0 p n D t c,
(forall x, m' x = m x) -> hd_inv regs0 m sp0 p n D t c -> hd_inv regs0 m' sp0 p n D t c.
Proof using.
intros regs0 m m' sp0 p n D t c Hx (HS & Wp & Wn & Wc & HC & HG).
assert (Hm : forall a, mbyte ubs0segs m' a = mbyte ubs0segs m a) by (intros a; unfold mbyte; rewrite Hx; reflexivity).
assert (HW : forall a v, word_mem ubs0segs m a v -> word_mem ubs0segs m' a v) by (intros a v W k Hk; rewrite Hm; apply W; exact Hk).
split; [apply (saved_ok_frame m m' sp0 regs0 HS); intros a _; apply Hm|].
split; [exact (HW _ _ Wp)|]. split; [exact (HW _ _ Wn)|]. split; [exact (HW _ _ Wc)|].
split; [intros j Hj; rewrite Hm; apply HC; exact Hj|].
apply (garr8_frame ubs0segs m m' p D HG). intros a _. apply Hm.
Qed.
Lemma hd_bytes : forall (m : word -> option byte) p D, garr8 ubs0segs m p D -> bytes_ok D.
Proof using.
intros m p D HG. unfold bytes_ok. apply Forall_forall. intros b Hb.
destruct (In_nth D b 0 Hb) as (j & Hj & <-). exact (proj2 (HG j Hj)).
Qed.
Lemma hd_call : forall E ss ms (regs0 : bvmap 5 word) L A mem md (p n s k fo : Z) (D : list Z) t (Q : config -> Prop),
fn_pre ubs0_msyms MR LIB_STACK L A regs0 mem md ->
st_ok ubs0segs E ss ms -> ss_pc ss = ubs0_A_readdata -> ss_resv ss = None ->
journal ubs0_msyms MR LIB_STACK (spZ regs0) [] L A mem md L A (ms_mem ms) md ->
getr (ms_regs ms) 10 = Z_to_bv 64 (spZ regs0 - 136) -> getr (ms_regs ms) 11 = Z_to_bv 64 (spZ regs0 - 80 + fo) ->
getr (ms_regs ms) 12 = Z_to_bv 64 k -> getr (ms_regs ms) 2 = Z_to_bv 64 (spZ regs0 - 144) ->
YK0s.ret_ok (getr (ms_regs ms) 1) ->
0 <= p < 2 ^ 64 -> 0 <= n -> (0 < n -> In (p, n) (blocks L A)) -> Z.of_nat (length D) = n ->
0 <= s -> 0 < k -> 0 <= fo -> fo + k <= 48 ->
(forall q, 0 <= q < k -> hd_cb D n t (fo + q) = 0) ->
hd_inv regs0 (ms_mem ms) (spZ regs0) p n D t (Z.min s n) ->
(forall (regs' : bvmap 5 word) (mem' : word -> option byte),
journal ubs0_msyms MR LIB_STACK (spZ regs0) [] L A mem md L A mem' md ->
regs_preserved (ms_regs ms) regs' ->
getr regs' 10 = Z_to_bv 64 (hd_rv (s + k <=? n)) ->
hd_inv regs0 mem' (spZ regs0) p n D ((fo, k, s) :: t) (Z.min (s + k) n) ->
SR ubs0segs (mkCfg (mkst regs' (getr (ms_regs ms) 1) mem' (seg_rom ubs0segs)) md) Q) ->
SR ubs0segs (mkCfg ms md) Q.
Proof using IMG LAWS.
intros E ss ms regs0 L A mem md p n s k fo D t Q HPRE HS Hpc Hrv HJ G10 G11 G12 G2 Hraw Hp Hn Hpin HL Hs Hk Hf0 Hf1 HZ HI K.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRD : RD_FRAME = 32) by reflexivity.
assert (HLS : LIB_STACK = 16384) by reflexivity.
pose proof HPRE as (HH & _ & (Hal16 & HSTK0 & Hceil & H63 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hq : exists q, sp0 = 16 * q) by (exists (sp0 / 16); pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
destruct Hq as [q Hq].
assert (Hpn : n = 0 \/ (4096 <= p /\ p + n <= alloc_ceiling)).
{ destruct (Z.eq_dec n 0) as [|Hnz]; [left; assumption|right].
destruct (heap_blocks_range _ _ LAWS L A mem md p n HH (Hpin ltac:(lia)) ltac:(lia)) as (H1 & H2 & _). lia. }
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHk.
destruct HI as (HSV & Wp & Wn & Wc & HC & HG).
eapply SR_bind.
{ eapply (jreaddata API IMG E ss ms LIB_STACK sp0 [] L A mem md L A md (sp0 - 136) (sp0 - 80 + fo) k p n (Z.min s n) (sp0 - 144)).
- exact HS. - exact Hpc. - exact Hrv. - exact HJ.
- exact G10. - exact G11. - exact G12. - exact G2.
- rewrite Hq. replace (16 * q - 144) with ((q - 9) * 16) by lia. apply Z.mod_mul. lia.
- rewrite HRD. lia. - lia. - exact H63.
- reflexivity. - exact Hraw.
- lia. - lia.
- rewrite Hq. replace (16 * q - 136) with ((2 * q - 17) * 8) by lia. apply Z.mod_mul. lia.
- exact Wp.
- replace (sp0 - 136 + 8) with (sp0 - 128) by lia. exact Wn.
- replace (sp0 - 136 + 16) with (sp0 - 120) by lia. exact Wc.
- lia. - destruct (Z.min_spec s n) as [[_ E1]|[_ E1]]; rewrite E1; lia.
- destruct Hpn; lia. - lia. - destruct Hpn; lia. - intros; destruct Hpn; lia.
- intros j Hj. exact (proj1 (heap_blocks _ _ LAWS L A _ md p n j HHk (Hpin ltac:(lia)) Hj)).
- lia. - lia.
- intros i Hi. apply UN0d.writable_off_img_present; [lia | unfold UN0d.in_img1; lia |].
apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
- intros a Ha. unfold wr_byte. left. lia.
- intros a Ha. unfold wr_byte. left. lia.
- right. lia. - right. lia.
- intros Hn0. left. rewrite HRD. destruct Hpn; lia.
- intros Hn0. left. destruct Hpn; lia.
- right. lia.
- intros Hn0. right. destruct Hpn; lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & HP2 & Hout2 & Hgr2 & Hcase2).
destruct (hd_rd_post (ms_mem ms) mem2 regs2 sp0 p n s k fo D t HL Hs Hk Hf0 Hf1 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(intros; destruct Hpn; lia) HG HC HZ Hout2 Hcase2) as (R10 & Wc2 & HC2 & HG2).
apply (K regs2 mem2 HJ2 HP2 R10).
unfold hd_inv, saved_ok in *. destruct HSV as (S1 & S2 & S3 & S4).
split; [repeat split|].
all: try (eapply hd_wm_rd; [exact Hout2 | lia | lia | rewrite HRD; lia | lia | lia | eassumption]).
split; [eapply hd_wm_rd; [exact Hout2 | lia | lia | rewrite HRD; lia | lia | lia | exact Wp]|].
split; [eapply hd_wm_rd; [exact Hout2 | lia | lia | rewrite HRD; lia | lia | lia | exact Wn]|].
split; [exact Wc2|]. split; [exact HC2 | exact HG2].
Qed.
Lemma hd_fr0 : forall E (m m' : word -> option byte), frame_of E [] m m' -> forall x, m' x = m x.
Proof using. intros E m m' HF x. apply HF. intros (r & [] & _). Qed.
Lemma hd_e2 : forall (rg : bvmap 5 word) sp0, getr rg 2 = Z_to_bv 64 (sp0 - 144) -> 0 <= sp0 - 144 < 2 ^ 64 ->
bv_unsigned (ew (Ereg rg []) 2) = sp0 - 144 /\ ew (Ereg rg []) 2 = Z_to_bv 64 (sp0 - 144).
Proof using.
intros rg sp0 H Hr. rewrite (ew_Ereg_nat rg [] 2 2%bv eq_refl), H. split; [apply unsigned_lit_small; exact Hr | reflexivity].
Qed.
Lemma hd_pres : forall (rA rB : bvmap 5 word), regs_preserved rA rB ->
getr rB 2 = getr rA 2 /\ getr rB 8 = getr rA 8 /\ getr rB 9 = getr rA 9 /\ getr rB 18 = getr rA 18.
Proof using.
intros rA rB HP.
split; [exact (HP 2 ltac:(unfold callee_saved; lia))|].
split; [exact (HP 8 ltac:(unfold callee_saved; lia))|].
split; [exact (HP 9 ltac:(unfold callee_saved; lia)) | exact (HP 18 ltac:(unfold callee_saved; lia))].
Qed.
Lemma hd_unt_call : forall (regs0 rA rB : bvmap 5 word), untouched_ok regs0 rA -> regs_preserved rA rB -> untouched_ok regs0 rB.
Proof using.
intros regs0 rA rB HU HP. unfold untouched_ok in *.
destruct HU as (U3 & U4 & U19 & U20 & U21 & U22 & U23 & U24 & U25 & U26 & U27).
rewrite <- U3, <- U4, <- U19, <- U20, <- U21, <- U22, <- U23, <- U24, <- U25, <- U26, <- U27.
repeat split.
- exact (HP 3 ltac:(unfold callee_saved; lia)).
- exact (HP 4 ltac:(unfold callee_saved; lia)).
- exact (HP 19 ltac:(unfold callee_saved; lia)).
- exact (HP 20 ltac:(unfold callee_saved; lia)).
- exact (HP 21 ltac:(unfold callee_saved; lia)).
- exact (HP 22 ltac:(unfold callee_saved; lia)).
- exact (HP 23 ltac:(unfold callee_saved; lia)).
- exact (HP 24 ltac:(unfold callee_saved; lia)).
- exact (HP 25 ltac:(unfold callee_saved; lia)).
- exact (HP 26 ltac:(unfold callee_saved; lia)).
- exact (HP 27 ltac:(unfold callee_saved; lia)).
Qed.
Lemma hd_unt_run : forall ss ms (regs0 rg : bvmap 5 word),
st_ok ubs0segs (Ereg rg []) ss ms -> untouched_ok regs0 rg ->
sr_get (ss_regs ss) (3%bv : reg) = SOff 3%nat 0 -> sr_get (ss_regs ss) (4%bv : reg) = SOff 4%nat 0 ->
sr_get (ss_regs ss) (19%bv : reg) = SOff 19%nat 0 -> sr_get (ss_regs ss) (20%bv : reg) = SOff 20%nat 0 ->
sr_get (ss_regs ss) (21%bv : reg) = SOff 21%nat 0 -> sr_get (ss_regs ss) (22%bv : reg) = SOff 22%nat 0 ->
sr_get (ss_regs ss) (23%bv : reg) = SOff 23%nat 0 -> sr_get (ss_regs ss) (24%bv : reg) = SOff 24%nat 0 ->
sr_get (ss_regs ss) (25%bv : reg) = SOff 25%nat 0 -> sr_get (ss_regs ss) (26%bv : reg) = SOff 26%nat 0 ->
sr_get (ss_regs ss) (27%bv : reg) = SOff 27%nat 0 ->
untouched_ok regs0 (ms_regs ms).
Proof using.
intros ss ms regs0 rg HS HU E3 E4 E19 E20 E21 E22 E23 E24 E25 E26 E27.
assert (HR : forall (r : reg) k, sr_get (ss_regs ss) r = SOff k 0 -> Z.of_nat k = bv_unsigned r -> getr (ms_regs ms) r = getr rg r).
{ intros r k Er Ek. rewrite (st_ok_reg ubs0segs _ ss ms r HS), Er. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
apply ew_Ereg_nat. exact Ek. }
unfold untouched_ok in *. destruct HU as (U3 & U4 & U19 & U20 & U21 & U22 & U23 & U24 & U25 & U26 & U27).
rewrite (HR _ _ E3 eq_refl), (HR _ _ E4 eq_refl), (HR _ _ E19 eq_refl), (HR _ _ E20 eq_refl), (HR _ _ E21 eq_refl),
(HR _ _ E22 eq_refl), (HR _ _ E23 eq_refl), (HR _ _ E24 eq_refl), (HR _ _ E25 eq_refl), (HR _ _ E26 eq_refl), (HR _ _ E27 eq_refl).
repeat split; assumption.
Qed.
Ltac hd_z := let q := fresh "q" in let Hq := fresh "Hq" in intros q Hq;
assert (q = 0 \/ q = 1 \/ q = 2 \/ q = 3) as [->|[->|[->| ->]]] by lia; reflexivity.
Ltac hd_enter HJ :=
lazymatch goal with |- SR _ (mkCfg (mkst ?rg (Z_to_bv 64 ?pc) ?mm _) _) _ =>
pose proof (hd_ss pc rg mm) as HS;
change mm with (ms_mem (mkst rg (Z_to_bv 64 pc) mm (seg_rom ubs0segs))) in HJ end.
Lemma hd_reads : forall (regs : bvmap 5 word) L A mem md (p n : Z) (PAYLOAD : list Z) (Q : config -> Prop)
(regs2 : bvmap 5 word) (mem2 : word -> option byte),
fn_pre ubs0_msyms MR LIB_STACK L A regs mem md -> 0 <= p < 2 ^ 64 -> 0 <= n ->
(0 < n -> In (p, n) (blocks L A)) ->
garr8 ubs0segs mem p PAYLOAD -> Z.of_nat (length PAYLOAD) = n ->
hd_mid regs L A mem md p n regs2 mem2 ->
(forall (regs1 : bvmap 5 word) (memc : word -> option byte),
journal ubs0_msyms MR LIB_STACK (spZ regs) [] L A mem md L A memc md ->
obj_at ubs0segs memc (spZ regs - 80) LAY_Config
[0; 0; lh_attr PAYLOAD n; lh_gen PAYLOAD n; lh_W PAYLOAD n; lh_H PAYLOAD n; lh_ngp PAYLOAD n; 0; 0; 0] ->
saved_ok memc (spZ regs) regs ->
word_mem ubs0segs memc (spZ regs - 136) p -> word_mem ubs0segs memc (spZ regs - 128) n ->
word_mem ubs0segs memc (spZ regs - 120) (lh_cur n) -> 0 <= lh_cur n <= n ->
getr regs1 2 = Z_to_bv 64 (spZ regs - 144) -> getr regs1 8 = Z_to_bv 64 (lh_r1 n) ->
getr regs1 10 = Z_to_bv 64 (lh_r2 n) ->
0 <= lh_r1 n < 2 ^ 64 -> 0 <= lh_r2 n < 2 ^ 64 ->
untouched_ok regs regs1 ->
(lh_r1 n = 0 -> lh_r2 n = 0 -> lh_cur n = 14 /\
hdr5 PAYLOAD = (false, (lh_W PAYLOAD n, lh_H PAYLOAD n, lh_attr PAYLOAD n, lh_gen PAYLOAD n, lh_ngp PAYLOAD n), skipn 14 PAYLOAD)) ->
(14 <= Z.of_nat (length PAYLOAD) -> lh_r1 n = 0 /\ lh_r2 n = 0) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_TAIL) memc (seg_rom ubs0segs)) md) Q) ->
SR ubs0segs (mkCfg (mkst regs2 (Z_to_bv 64 L_HD1) mem2 (seg_rom ubs0segs)) md) Q.
Proof using IMG LAWS.
intros regs L A mem md p n D Q regs2 mem2 HPRE Hp Hn Hpin HPL HPLn Hmid K.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLS : LIB_STACK = 16384) by reflexivity.
pose proof HPRE as (HH & _ & (Hal16 & HSTK0 & Hceil & H63 & Hstw) & _).
destruct Hmid as (HJ & Hgr & Hfr & HSV & Wp & Wn & Wc & Hz & G2 & HU).
assert (Hpn : n = 0 \/ (4096 <= p /\ p + n <= alloc_ceiling)).
{ destruct (Z.eq_dec n 0) as [|Hnz]; [left; assumption|right].
destruct (heap_blocks_range _ _ LAWS L A mem md p n HH (Hpin ltac:(lia)) ltac:(lia)) as (H1 & H2 & _). lia. }
set (sp0 := spZ regs) in *.
pose proof (hd_bytes mem p D HPL) as HB.
assert (HI0 : hd_inv regs mem2 sp0 p n D [] (Z.min 0 n)).
{ rewrite Z.min_l by lia. split; [exact HSV|]. split; [exact Wp|]. split; [exact Wn|]. split; [exact Wc|]. split.
- intros j Hj. exact (Hz j Hj).
- apply (garr8_frame ubs0segs mem mem2 p D HPL). intros a Ha. rewrite HPLn in Ha. unfold mbyte.
rewrite (Hfr (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by (destruct Hpn; lia). destruct Hpn; lia. }
hd_enter HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_readdata.
{ wr_norm. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (HUm : untouched_ok regs (ms_regs ms)) by (eapply hd_unt_run; [exact HS | exact HU | reflexivity ..]).
destruct (hd_e2 regs2 sp0 G2 ltac:(lia)) as [E2u E2w].
jreg HS (10%bv:reg) as M10. jreg HS (11%bv:reg) as M11. jreg HS (12%bv:reg) as M12.
jreg HS (2%bv:reg) as M2. jreg HS (1%bv:reg) as M1.
rewrite E2u in M10, M11. rewrite E2w in M2.
replace (sp0 - 144 + 8) with (sp0 - 136) in M10 by lia.
replace (sp0 - 144 + 88) with (sp0 - 80 + 24) in M11 by lia.
apply (hd_call _ _ _ regs L A mem md p n 0 2 24 D [] Q HPRE HS eq_refl eq_refl HJ M10 M11 M12 M2
ltac:(rewrite M1; apply ret_ok_even; vm_compute; reflexivity) Hp Hn Hpin HPLn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(hd_z) (hd_inv_eq _ _ _ _ _ _ _ _ _ (hd_fr0 _ _ _ HF) HI0)).
intros regs3 mem3 HJ3 HP3 R3 HI3. rewrite M1.
destruct (hd_pres _ _ HP3) as (P2 & _ & _ & _).
pose proof (hd_unt_call _ _ _ HUm HP3) as HU3.
assert (G3 : getr regs3 2 = Z_to_bv 64 (sp0 - 144)) by (rewrite P2; exact M2).
clear HS HJ HF HG HUm E2u E2w M10 M11 M12 M2 M1 P2 HP3 HI0 ms.
hd_enter HJ3.
jrun_to LAWS ubs0tbl_ok HS HJ3 ubs0_A_readdata.
{ wr_norm. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (HUm : untouched_ok regs (ms_regs ms)) by (eapply hd_unt_run; [exact HS | exact HU3 | reflexivity ..]).
destruct (hd_e2 regs3 sp0 G3 ltac:(lia)) as [E2u E2w].
jreg HS (10%bv:reg) as M10. jreg HS (11%bv:reg) as M11. jreg HS (12%bv:reg) as M12.
jreg HS (2%bv:reg) as M2. jreg HS (1%bv:reg) as M1. jreg HS (8%bv:reg) as N8.
rewrite E2u in M10, M11. rewrite E2w in M2. rewrite (ew_Ereg_nat regs3 [] 10 10%bv eq_refl), R3 in N8.
replace (sp0 - 144 + 8) with (sp0 - 136) in M10 by lia.
replace (sp0 - 144 + 90) with (sp0 - 80 + 26) in M11 by lia.
apply (hd_call _ _ _ regs L A mem md p n 2 2 26 D [(24, 2, 0)] Q HPRE HS eq_refl eq_refl HJ3 M10 M11 M12 M2
ltac:(rewrite M1; apply ret_ok_even; vm_compute; reflexivity) Hp Hn Hpin HPLn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(hd_z) (hd_inv_eq _ _ _ _ _ _ _ _ _ (hd_fr0 _ _ _ HF) HI3)).
intros regs4 mem4 HJ4 HP4 R4 HI4. rewrite M1.
destruct (hd_pres _ _ HP4) as (P2 & P8 & _ & _).
pose proof (hd_unt_call _ _ _ HUm HP4) as HU4.
assert (G4 : getr regs4 2 = Z_to_bv 64 (sp0 - 144)) by (rewrite P2; exact M2).
assert (X8_4 : getr regs4 8 = Z_to_bv 64 (hd_rv (0 + 2 <=? n))) by (rewrite P8; exact N8).
clear HS HJ3 HF HG HUm E2u E2w M10 M11 M12 M2 M1 N8 P2 P8 HP4 HI3 ms.
hd_enter HJ4.
jrun_to LAWS ubs0tbl_ok HS HJ4 ubs0_A_readdata.
{ wr_norm. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (HUm : untouched_ok regs (ms_regs ms)) by (eapply hd_unt_run; [exact HS | exact HU4 | reflexivity ..]).
destruct (hd_e2 regs4 sp0 G4 ltac:(lia)) as [E2u E2w].
jreg HS (10%bv:reg) as M10. jreg HS (11%bv:reg) as M11. jreg HS (12%bv:reg) as M12.
jreg HS (2%bv:reg) as M2. jreg HS (1%bv:reg) as M1. jreg HS (8%bv:reg) as N8. jreg HS (9%bv:reg) as N9.
rewrite E2u in M10, M11. rewrite E2w in M2.
rewrite (ew_Ereg_nat regs4 [] 8 8%bv eq_refl), X8_4 in N8. rewrite (ew_Ereg_nat regs4 [] 10 10%bv eq_refl), R4 in N9.
replace (sp0 - 144 + 8) with (sp0 - 136) in M10 by lia.
replace (sp0 - 144 + 80) with (sp0 - 80 + 16) in M11 by lia.
apply (hd_call _ _ _ regs L A mem md p n 4 4 16 D [(26, 2, 2); (24, 2, 0)] Q HPRE HS eq_refl eq_refl HJ4 M10 M11 M12 M2
ltac:(rewrite M1; apply ret_ok_even; vm_compute; reflexivity) Hp Hn Hpin HPLn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(hd_z) (hd_inv_eq _ _ _ _ _ _ _ _ _ (hd_fr0 _ _ _ HF) HI4)).
intros regs5 mem5 HJ5 HP5 R5 HI5. rewrite M1.
destruct (hd_pres _ _ HP5) as (P2 & P8 & P9 & _).
pose proof (hd_unt_call _ _ _ HUm HP5) as HU5.
assert (G5 : getr regs5 2 = Z_to_bv 64 (sp0 - 144)) by (rewrite P2; exact M2).
assert (X8_5 : getr regs5 8 = Z_to_bv 64 (hd_rv (0 + 2 <=? n))) by (rewrite P8; exact N8).
assert (X9_5 : getr regs5 9 = Z_to_bv 64 (hd_rv (2 + 2 <=? n))) by (rewrite P9; exact N9).
clear HS HJ4 HF HG HUm E2u E2w M10 M11 M12 M2 M1 N8 N9 P2 P8 P9 HP5 HI4 X8_4 ms.
hd_enter HJ5.
jrun_to LAWS ubs0tbl_ok HS HJ5 ubs0_A_readdata.
{ wr_norm. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (HUm : untouched_ok regs (ms_regs ms)) by (eapply hd_unt_run; [exact HS | exact HU5 | reflexivity ..]).
destruct (hd_e2 regs5 sp0 G5 ltac:(lia)) as [E2u E2w].
jreg HS (10%bv:reg) as M10. jreg HS (11%bv:reg) as M11. jreg HS (12%bv:reg) as M12.
jreg HS (2%bv:reg) as M2. jreg HS (1%bv:reg) as M1.
jreg HS (8%bv:reg) as N8. jreg HS (9%bv:reg) as N9. jreg HS (18%bv:reg) as N18.
rewrite E2u in M10, M11. rewrite E2w in M2.
rewrite (ew_Ereg_nat regs5 [] 8 8%bv eq_refl), X8_5 in N8. rewrite (ew_Ereg_nat regs5 [] 9 9%bv eq_refl), X9_5 in N9.
rewrite (ew_Ereg_nat regs5 [] 10 10%bv eq_refl), R5 in N18.
replace (sp0 - 144 + 8) with (sp0 - 136) in M10 by lia.
replace (sp0 - 144 + 84) with (sp0 - 80 + 20) in M11 by lia.
apply (hd_call _ _ _ regs L A mem md p n 8 4 20 D [(16, 4, 4); (26, 2, 2); (24, 2, 0)] Q HPRE HS eq_refl eq_refl HJ5 M10 M11 M12 M2
ltac:(rewrite M1; apply ret_ok_even; vm_compute; reflexivity) Hp Hn Hpin HPLn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(hd_z) (hd_inv_eq _ _ _ _ _ _ _ _ _ (hd_fr0 _ _ _ HF) HI5)).
intros regs6 mem6 HJ6 HP6 R6 HI6. rewrite M1.
destruct (hd_pres _ _ HP6) as (P2 & P8 & P9 & P18).
pose proof (hd_unt_call _ _ _ HUm HP6) as HU6.
assert (G6 : getr regs6 2 = Z_to_bv 64 (sp0 - 144)) by (rewrite P2; exact M2).
assert (X8_6 : getr regs6 8 = Z_to_bv 64 (hd_rv (0 + 2 <=? n))) by (rewrite P8; exact N8).
assert (X9_6 : getr regs6 9 = Z_to_bv 64 (hd_rv (2 + 2 <=? n))) by (rewrite P9; exact N9).
assert (X18_6 : getr regs6 18 = Z_to_bv 64 (hd_rv (4 + 4 <=? n))) by (rewrite P18; exact N18).
clear HS HJ5 HF HG HUm E2u E2w M10 M11 M12 M2 M1 N8 N9 N18 P2 P8 P9 P18 HP6 HI5 X8_5 X9_5 ms.
hd_enter HJ6.
jrun_to LAWS ubs0tbl_ok HS HJ6 ubs0_A_readdata.
{ wr_norm. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (HUm : untouched_ok regs (ms_regs ms)) by (eapply hd_unt_run; [exact HS | exact HU6 | reflexivity ..]).
destruct (hd_e2 regs6 sp0 G6 ltac:(lia)) as [E2u E2w].
jreg HS (10%bv:reg) as M10. jreg HS (11%bv:reg) as M11. jreg HS (12%bv:reg) as M12.
jreg HS (2%bv:reg) as M2. jreg HS (1%bv:reg) as M1. jreg HS (8%bv:reg) as N8.
rewrite E2u in M10, M11. rewrite E2w in M2.
rewrite (ew_Ereg_nat regs6 [] 8 8%bv eq_refl), (ew_Ereg_nat regs6 [] 9 9%bv eq_refl), (ew_Ereg_nat regs6 [] 18 18%bv eq_refl),
(ew_Ereg_nat regs6 [] 10 10%bv eq_refl), X8_6, X9_6, X18_6, R6 in N8.
replace (sp0 - 144 + 8) with (sp0 - 136) in M10 by lia.
replace (sp0 - 144 + 92) with (sp0 - 80 + 28) in M11 by lia.
apply (hd_call _ _ _ regs L A mem md p n 12 2 28 D [(20, 4, 8); (16, 4, 4); (26, 2, 2); (24, 2, 0)] Q HPRE HS eq_refl eq_refl HJ6
M10 M11 M12 M2 ltac:(rewrite M1; apply ret_ok_even; vm_compute; reflexivity) Hp Hn Hpin HPLn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(hd_z) (hd_inv_eq _ _ _ _ _ _ _ _ _ (hd_fr0 _ _ _ HF) HI6)).
intros regs7 mem7 HJ7 HP7 R7 HI7. rewrite M1.
destruct (hd_pres _ _ HP7) as (P2 & P8 & _ & _).
destruct HI7 as (HSV7 & Wp7 & Wn7 & Wc7 & HC7 & HG7).
apply (K regs7 mem7 HJ7 (hd_obj mem7 (sp0 - 80) D n HB HC7) HSV7 Wp7 Wn7 Wc7).
- unfold lh_cur. lia.
- rewrite P2. exact M2.
- rewrite P8, N8. unfold lh_r1. apply bv_eq. cbn [alu64 alu]. rewrite !bv_or_unsigned.
destruct (0 + 2 <=? n) eqn:B1; destruct (2 + 2 <=? n) eqn:B2; destruct (4 + 4 <=? n) eqn:B3;
destruct (8 + 4 <=? n) eqn:B4; destruct (12 <=? n) eqn:B5;
first [reflexivity | exfalso; repeat match goal with
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end; lia].
- rewrite R7. reflexivity.
- unfold lh_r1. destruct (12 <=? n); lia.
- unfold lh_r2. destruct (14 <=? n); lia.
- exact (hd_unt_call _ _ _ HUm HP7).
- exact (hd_hdr D n HPLn).
- intros H14. rewrite HPLn in H14. unfold lh_r1, lh_r2.
rewrite (proj2 (Z.leb_le 12 n)), (proj2 (Z.leb_le 14 n)) by lia. split; reflexivity.
Qed.
Lemma lh_hdr : forall (regs : bvmap 5 word) L A mem md (p n : Z) (PAYLOAD : list Z) (Q : config -> Prop),
fn_pre ubs0_msyms MR LIB_STACK L A regs mem md ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 <= p < 2 ^ 64 -> 0 <= n ->
(0 < n -> In (p, n) (blocks L A)) ->
garr8 ubs0segs mem p PAYLOAD -> Z.of_nat (length PAYLOAD) = n ->
(forall (regs1 : bvmap 5 word) (memc : word -> option byte),
journal ubs0_msyms MR LIB_STACK (spZ regs) [] L A mem md L A memc md ->
obj_at ubs0segs memc (spZ regs - 80) LAY_Config
[0; 0; lh_attr PAYLOAD n; lh_gen PAYLOAD n; lh_W PAYLOAD n; lh_H PAYLOAD n; lh_ngp PAYLOAD n; 0; 0; 0] ->
saved_ok memc (spZ regs) regs ->
word_mem ubs0segs memc (spZ regs - 136) p -> word_mem ubs0segs memc (spZ regs - 128) n ->
word_mem ubs0segs memc (spZ regs - 120) (lh_cur n) -> 0 <= lh_cur n <= n ->
getr regs1 2 = Z_to_bv 64 (spZ regs - 144) -> getr regs1 8 = Z_to_bv 64 (lh_r1 n) ->
getr regs1 10 = Z_to_bv 64 (lh_r2 n) ->
0 <= lh_r1 n < 2 ^ 64 -> 0 <= lh_r2 n < 2 ^ 64 ->
untouched_ok regs regs1 ->
(lh_r1 n = 0 -> lh_r2 n = 0 -> lh_cur n = 14 /\
hdr5 PAYLOAD = (false, (lh_W PAYLOAD n, lh_H PAYLOAD n, lh_attr PAYLOAD n, lh_gen PAYLOAD n, lh_ngp PAYLOAD n), skipn 14 PAYLOAD)) ->
(14 <= Z.of_nat (length PAYLOAD) -> lh_r1 n = 0 /\ lh_r2 n = 0) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_TAIL) memc (seg_rom ubs0segs)) md) Q) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom ubs0segs)) md) Q.
Proof using IMG LAWS.
intros regs L A mem md p n PAYLOAD Q HPRE G10 G11 Hp Hn Hpin HPL HPLn K.
assert (Hn64 : n < 2 ^ 64).
{ destruct (Z.eq_dec n 0) as [->|Hnz]; [lia|].
pose proof HPRE as (HH & _).
destruct (heap_blocks_range _ _ LAWS L A mem md p n HH (Hpin ltac:(lia)) ltac:(lia)) as (_ & Hpn & _).
pose proof alloc_ceiling_lt. lia. }
apply (hd_pro regs L A mem md p n Q HPRE G10 G11 Hp ltac:(lia)).
intros regs2 mem2 Hmid.
exact (hd_reads regs L A mem md p n PAYLOAD Q regs2 mem2 HPRE Hp Hn Hpin HPL HPLn Hmid K).
Qed.
End S.
End c.
