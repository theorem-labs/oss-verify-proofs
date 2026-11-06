(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Export AsanEmbed.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition KLOW : Z := 0x7fff8000.
Definition KHIGH : Z := 0x10007fff8000.
Definition KEND : Z := 0x800000000000.
Lemma shad_div : forall a, shad a = ASHOFF + a / 8.
Proof. intros a. unfold shad. Local Ltac2 Set LiaHints.tbl := fun () => "0010=29781691149.1000001S".
rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition blockf (p n : Z) (s : Z) : Z :=
let g := s - shad p in if 8 * g + 8 <=? n then 0 else n - 8 * g.
Definition nshad (n : Z) : Z := Z.shiftr (n + 7) 3.
Lemma nshad_div : forall n, nshad n = (n + 7) / 8.
Proof. intros. unfold nshad. Local Ltac2 Set LiaHints.tbl := fun () => "0010=29781872000.1000001S".
rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. rewrite !shad_div. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.
Definition app_blk (lo hi : Z) : Prop :=
lo <= hi /\ ((0 <= lo /\ hi + 8 <= KLOW) \/ (KHIGH <= lo /\ hi + 8 <= KEND)).
Lemma app_blk_sub : forall lo hi lo' hi', app_blk lo hi -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> app_blk lo' hi'.
Proof. intros lo hi lo' hi' [H1 H2] A B C. Local Ltac2 Set LiaHints.tbl := fun () => "0020=48982726145.99414640046.9 00000300;S1BS2H21A1C".
split; [lia|]. unfold KLOW, KHIGH, KEND in *. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition sval (b : byte) : Z := bv_signed b.
Definition gran_ok (need : Z) (b : byte) : Prop := sval b = 0 \/ need <= sval b <= 7.
Lemma gran_ok_mono : forall n n' b, gran_ok n b -> n' <= n -> gran_ok n' b.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010=32656765169.5000007S1H3Hle".
intros n n' b [H|H] Hle; [left; exact H| right; lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma gran_ok_full : forall n b, gran_ok n b -> 8 <= n -> b = Z_to_bv 8 0.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=25739456168.4000006S1H2Hn".
intros n b [H|H] Hn; [|lia]. unfold sval in H. apply bv_eq_signed. rewrite H. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sval_zero : sval (Z_to_bv 8 0) = 0. Proof. reflexivity. Qed.
Lemma sval_lit : forall k, 0 <= k <= 127 -> sval (Z_to_bv 8 k) = k.
Proof.
intros k Hk. unfold sval. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (Z.of_N 8 - 1) with 7. change (2^7) with 128. Local Ltac2 Set LiaHints.tbl := fun () => "0020=22790098710.29222259456.2 000001005SS2Hk".
rewrite Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sval_range : forall b : byte, -128 <= sval b <= 127.
Proof.
intros b. unfold sval, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (Z.of_N 8 - 1) with 7. change (2^7) with 128.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=18435742460.12586041737.2 000001002SS".
pose proof (Z.mod_pos_bound (bv_unsigned b + 128) 256 ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land7_mod : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). Local Ltac2 Set LiaHints.tbl := fun () => "0010=29782099606.1000001S".
rewrite Z.land_ones by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma signed_lit_small64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with (2^64). change (2 ^ (Z.of_N 64 - 1)) with (2^63).
Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>43526548600.1600000?S2Hz1H2H02H42H5".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sxb_sval : forall b : byte, sxb b = Z_to_bv 64 (sval b).
Proof. reflexivity. Qed.
Section WithSegs.
Variable segs : list Segment.
Definition shadow_bytes (m : word -> option byte) (s1 s2 : Z) (f : Z -> Z) : Prop :=
0 <= s1 /\ s2 <= 2^64 /\ forall s, s1 <= s < s2 -> m (wa s) = Some (Z_to_bv 8 (f s)).
#[using="Type"] Lemma shadow_bytes_sub : forall m s1 s2 f s1' s2',
shadow_bytes m s1 s2 f -> s1 <= s1' -> s2' <= s2 -> shadow_bytes m s1' s2' f.
Proof. intros m s1 s2 f s1' s2' (A & B & H) H1 H2. Local Ltac2 Set LiaHints.tbl := fun () => "0030>1622514908.12 16829217265.1253701529329.1400000600<00FS1B2H2S1A2H1S2H12H22Hs".
split; [lia|]. split; [lia|]. intros s Hs. apply H. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shadow_bytes_ext : forall m s1 s2 f g,
shadow_bytes m s1 s2 f -> (forall s, s1 <= s < s2 -> Z_to_bv 8 (f s) = Z_to_bv 8 (g s)) -> shadow_bytes m s1 s2 g.
Proof. intros m s1 s2 f g (A & B & H) E. Local Ltac2 Set LiaHints.tbl := fun () => "0030>14082955192.1039425022174.1053701529329.1200000300600:S1BS1AS2Hs".
split; [lia|]. split; [lia|]. intros s Hs. rewrite H, E by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shadow_bytes_agree : forall m m' s1 s2 f,
shadow_bytes m s1 s2 f -> (forall s, s1 <= s < s2 -> m' (wa s) = m (wa s)) -> shadow_bytes m' s1 s2 f.
Proof. intros m m' s1 s2 f (A & B & H) E. Local Ltac2 Set LiaHints.tbl := fun () => "0030>14082955192.1039425022174.1053701529329.1200000300600:S1BS1AS2Hs".
split; [lia|]. split; [lia|]. intros s Hs. rewrite E by lia. apply H. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shadow_bytes_munch : forall W m m' s1 s2 f,
shadow_bytes m s1 s2 f -> munch W m m' -> disjoint_from W s1 (s2 - s1) -> shadow_bytes m' s1 s2 f.
Proof.
intros W m m' s1 s2 f SB MU D. pose proof SB as (A & B & _). eapply shadow_bytes_agree; [exact SB|].
intros s Hs. apply MU. eapply disjoint_outside; [exact D|]. Local Ltac2 Set LiaHints.tbl := fun () => "0020>18614817987.1449314540127.1400000800<S1A1B2HsS2Hs".
rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition no_image (s1 s2 : Z) : Prop := forall z, s1 <= z < s2 -> find_segment segs z 1 = None.
#[using="Type"] Lemma mrd_no_image : forall m s1 s2 s, no_image s1 s2 -> s1 <= s < s2 -> 0 <= s1 -> s2 <= 2^64 ->
mrd segs m (wa s) = m (wa s).
Proof.
intros m s1 s2 s NI Hs A B. unfold mrd. destruct (m (wa s)); [reflexivity|].
unfold seg_rom, memory_read. Local Ltac2 Set LiaHints.tbl := fun () => "0020=18620944180.953699597574.900000800<S2Hs1A1BS2Hs".
rewrite wa_unsigned by lia. change (Z.of_N 1) with 1. rewrite (NI s) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma wview_no_image : forall m s1 s2 s, no_image s1 s2 -> s1 <= s < s2 -> 0 <= s1 -> s2 <= 2^64 ->
wview segs m (wa s) = m (wa s).
Proof.
intros m s1 s2 s NI Hs A B. unfold wview. destruct (m (wa s)); [reflexivity|].
Local Ltac2 Set LiaHints.tbl := fun () => "0020=18620944180.953699597574.900000800<S2Hs1A1BS2Hs".
rewrite wa_unsigned by lia. rewrite (NI s) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition shadow_list (s : Z) (n : nat) (f : Z -> Z) : list byte :=
map (fun i => Z_to_bv 8 (f (s + Z.of_nat i))) (seq 0 n).
#[using="Type"] Lemma shadow_list_length : forall s n f, length (shadow_list s n f) = n.
Proof. intros. unfold shadow_list. rewrite length_map, length_seq. reflexivity. Qed.
#[using="Type"] Lemma shadow_list_nth : forall s n f i, (i < n)%nat ->
nth_error (shadow_list s n f) i = Some (Z_to_bv 8 (f (s + Z.of_nat i))).
Proof.
intros s n f i Hi. unfold shadow_list. rewrite nth_error_map, nth_error_seq. Local Ltac2 Set LiaHints.tbl := fun () => "0010=29439415156.7000007S2Hi2n0".
destruct (PeanoNat.Nat.ltb_spec0 i n); [reflexivity| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma bytes_at_of_shadow_bytes : forall m s1 s2 f,
shadow_bytes m s1 s2 f -> s1 <= s2 -> bytes_at segs m s1 (shadow_list s1 (Z.to_nat (s2 - s1)) f).
Proof.
intros m s1 s2 f (A & B & H) Hle. Local Ltac2 Set LiaHints.tbl := fun () => "0040>34409181698.1139420775742.9 60121492168.9 67487841421.1100000400700>00BS2HiS1AS1B3HleS2Hi".
split; [lia|]. split. { rewrite shadow_list_length. lia. }
intros i Hi. rewrite shadow_list_length in Hi. rewrite shadow_list_nth by lia.
unfold mrd. rewrite H by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rw_cells_C1_of_byte : forall m s b, 0 <= s -> s + 1 <= 2^64 -> m (wa s) = Some b -> rw_cells segs m s [C1 b].
Proof.
intros m s b A B H. split; [split|].
- cbn. split; exact I.
- cbn [cells_bytes cbytes app]. Local Ltac2 Set LiaHints.tbl := fun () => "0040=11863645839.718951859023.925602808726.751388266601.900000300700:00>S1AS2HiS1BS2Hi".
split; [lia|]. split; [cbn; lia|].
intros [|i] Hi; cbn in Hi; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. unfold mrd. rewrite H. reflexivity.
- cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. replace (s + i) with s by lia.
unfold wview. rewrite H. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma wr_at_some : forall m s n i, wr_at segs m s n -> no_image s (s + n) -> 0 <= i < n ->
exists b, m (wa (s + i)) = Some b.
Proof.
intros m s n i (A & B & H) NI Hi. specialize (H i Hi).
Local Ltac2 Set LiaHints.tbl := fun () => "0010=3696609647.10000004S2Hi".
rewrite (wview_no_image m s (s + n)) in H by (auto; lia).
destruct (m (wa (s + i))) as [b|]; [exists b; reflexivity| congruence].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rw_cells_of_wr_at : forall m s n, wr_at segs m s n -> no_image s (s + n) -> 0 <= n ->
exists bs, length bs = Z.to_nat n /\ rw_cells segs m s [CB (Z.to_nat n) bs].
Proof.
intros m s n W NI Hn. pose proof W as (A & B & _).
assert (G : forall k : nat, (Z.of_nat k <= n) -> exists bs, length bs = k /\
forall i, (i < k)%nat -> mrd segs m (wa (s + Z.of_nat i)) = nth_error bs i).
{ induction k as [|k IH]; intros Hk.
- exists []. split; [reflexivity|]. Local Ltac2 Set LiaHints.tbl := fun () => "00=0>10303021478.2010570710229.1211867835378.1313009055992.1513022891787.2023268674726.1229878941859.1833096366097.103429175868.15 46604852553.1854978904071.1360947881832.1366519703517.1700000?00F00N00W00f00j01601:01C01O01X01c01lS2Hk4Hlen2Hi2n0S2Hk2HiS1A4HlenS2Hk4HlenS2Hk4Hlen2Hi2n0S2HkS2Hk4Hlen2HiS2HnS4Hlen2HiS2Hk4Hlen2HiS2Hn4HlenS2Hn1B4HlenS2Hk4Hlen".
intros i Hi; lia.
- destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
destruct (wr_at_some m s n (Z.of_nat k) W NI ltac:(lia)) as [b Hb].
exists (bs ++ [b]). split. { rewrite length_app; cbn; lia. }
intros i Hi. destruct (Nat.eqb_spec i k).
+ subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. cbn.
rewrite (mrd_no_image m s (s + n)) by (auto; lia). exact Hb.
+ rewrite nth_error_app1 by lia. apply Hbs. lia. }
destruct (G (Z.to_nat n) ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
split; [split|].
- cbn. rewrite Hlen. split; [reflexivity| exact I].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [lia|]. split; [rewrite Hlen; lia|].
intros i Hi. apply Hbs. lia.
- cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. replace (Z.of_nat (Z.to_nat n)) with n by lia. exact W.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as HR.
Local Ltac2 Set LiaHints.tbl := fun () => "0030=21374819047.663368328716.668399281967.6000004005009S2HbSS2HR".
rewrite lor_shiftl8_add by lia.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8). change (2^8) with 256.
Z.div_mod_to_equations. nia.
- rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; nia).
apply IH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_bound bs) as HR. pose proof (bytes_le_to_Z_nonneg bs) as H0. rewrite HL in HR.
change (2 ^ (8 * Z.of_nat 8)) with (2^64) in HR.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=10821511094.500000:S2HL2HR2H0".
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia). rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rw_cells_C8_of_wr_at : forall m s, wr_at segs m s 8 -> no_image s (s + 8) ->
exists w : word, rw_cells segs m s [C8 w].
Proof.
intros m s W NI. Local Ltac2 Set LiaHints.tbl := fun () => "0010=63368231573.5000001S".
destruct (rw_cells_of_wr_at m s 8 W NI ltac:(lia)) as (bs & Hlen & R).
exists (le_bytes_to_word bs).
destruct R as [[_ Hb] Hw]. split; [split|].
- cbn. split; [reflexivity| exact I].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb.
rewrite le8_of_bytes by exact Hlen. exact Hb.
- exact Hw.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition unpoisoned (m : word -> option byte) (lo hi : Z) : Prop :=
0 <= lo /\ hi <= 2^64 /\
forall G, lo < hi -> lo <= 8 * G + 7 -> 8 * G < hi ->
exists b, m (wa (ASHOFF + G)) = Some b /\ gran_ok (Z.min (8 * G + 8) hi - 8 * G) b.
#[using="Type"] Lemma unpoisoned_sub : forall m lo hi lo' hi',
unpoisoned m lo hi -> lo <= lo' -> hi' <= hi -> unpoisoned m lo' hi'.
Proof.
intros m lo hi lo' hi' (A & B & H) H1 H2. Local Ltac2 Set LiaHints.tbl := fun () => "0060>14838513244.153363052655.18 5689100529.11 58527028180.1563589884723.1563762581852.1100000800<00B00M00U00[S2H13HG1S2H2S1A2H1S2H12H23HG0S2H23HG2S1B2H2".
split; [lia|]. split; [lia|].
intros G HG0 HG1 HG2. destruct (H G ltac:(lia) ltac:(lia) ltac:(lia)) as (b & Hb & Hok).
exists b. split; [exact Hb|]. eapply gran_ok_mono; [exact Hok|]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unpoisoned_nil : forall m lo, 0 <= lo <= 2^64 -> unpoisoned m lo lo.
Proof. intros m lo A. Local Ltac2 Set LiaHints.tbl := fun () => "0030=29432519000.457858519866.858772157733.400000300700:S1AS2H0S1A".
split; [lia|]. split; [lia|]. intros G H0 H1 H2. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unpoisoned_agree : forall m m' lo hi,
unpoisoned m lo hi -> (forall s, shad lo <= s <= shad (hi - 1) -> m' (wa s) = m (wa s)) -> unpoisoned m' lo hi.
Proof.
intros m m' lo hi (A & B & H) E. Local Ltac2 Set LiaHints.tbl := fun () => "0030>13219203330.3029432585052.9 52365312927.9 00000C00F00IS2H12H22H32H42H82H9S1AS1B".
split; [lia|]. split; [lia|]. intros G H0 H1 H2.
destruct (H G H0 H1 H2) as (b & Hb & Hok). exists b. split; [|exact Hok].
rewrite E; [exact Hb|]. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unpoisoned_munch : forall W m m' lo hi,
unpoisoned m lo hi -> munch W m m' -> disjoint_from W (shad lo) (shad (hi - 1) + 1 - shad lo) -> unpoisoned m' lo hi.
Proof.
intros W m m' lo hi U MU D. pose proof U as (A & B & _). eapply unpoisoned_agree; [exact U|].
intros s Hs. apply MU. eapply disjoint_outside; [exact D|].
rewrite !shad_div in *. unfold ASHOFF in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>18614825486.2758613351006.1300000C00GS1A1B2Hs1H2H02H42H5S2Hs".
rewrite wa_unsigned by (Z.div_mod_to_equations; lia). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unpoisoned_byte : forall m lo hi a,
unpoisoned m lo hi -> lo <= a < hi ->
exists b, m (wa (shad a)) = Some b /\ gran_ok (Z.min (8 * (a / 8) + 8) hi - 8 * (a / 8)) b.
Proof.
intros m lo hi a (A & B & H) Ha. rewrite shad_div.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>11369135956.1647137473683.1658524927621.9 00000:00D00HS2Ha2H02H1S2Ha2H02H1S2Ha".
apply (H (a / 8)); Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unpoisoned_check : forall m lo hi a N,
unpoisoned m lo hi -> lo <= a -> a + N <= hi -> 1 <= N -> a mod 8 + N <= 8 ->
exists b, rw_cells segs m (shad a) [C1 b] /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + N - 1 < sval b)).
Proof.
intros m lo hi a N U H1 H2 H3 H4. pose proof U as (A & B & _).
Local Ltac2 Set LiaHints.tbl := fun () => "0040>1053474926.23 10627721995.1325606867181.2362419118911.2300000?00I00T00bS2H22H32Hk1H2H0S2H12H22H3S2H11A1H2H0S2H22H31B1H2H0".
destruct (unpoisoned_byte m lo hi a U ltac:(lia)) as (b & Hb & Hok).
exists b. split.
- apply rw_cells_C1_of_byte; [| |exact Hb]; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
- destruct Hok as [Z0|Hk]; [left; exact Z0| right]. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unpoisoned_full : forall m lo hi G,
unpoisoned m lo hi -> lo <= 8 * G + 7 -> 8 * G + 8 <= hi -> m (wa (ASHOFF + G)) = Some (Z_to_bv 8 0).
Proof.
intros m lo hi G (A & B & H) H1 H2. Local Ltac2 Set LiaHints.tbl := fun () => "0040>14836401116.1058524937812.1063591980723.1068531508714.1300000400;00?00CS2H1S2H12H2S2H2S2H2".
destruct (H G ltac:(lia) ltac:(lia) ltac:(lia)) as (b & Hb & Hok).
rewrite Hb. f_equal. eapply gran_ok_full; [exact Hok|]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unpoisoned_core_zero : forall m lo hi lo' hi',
unpoisoned m lo hi -> lo <= lo' -> hi' <= hi -> lo' mod 8 = 0 -> hi' mod 8 = 0 -> lo' <= hi' ->
shadow_bytes m (shad lo') (shad hi') (fun _ => 0).
Proof.
intros m lo hi lo' hi' U H1 H2 A1 A2 LE. pose proof U as (A & B & _).
rewrite !shad_div. split. { Local Ltac2 Set LiaHints.tbl := fun () => "0050>25608965604.2825914225759.2830374776203.1635669598209.30470058213.30  00000;00F00G00T00`S2H12A11A1HS2H22A21B1HSS2H22A22Hs2H6S2H12A12Hs1H".
unfold ASHOFF; Z.div_mod_to_equations; lia. } split. { unfold ASHOFF; Z.div_mod_to_equations; lia. }
intros s Hs. replace s with (ASHOFF + (s - ASHOFF)) at 1 by lia.
apply (unpoisoned_full m lo hi (s - ASHOFF) U); Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition shadow_block (m : word -> option byte) (p n : Z) : Prop :=
p mod 8 = 0 /\ 0 <= p /\ 0 <= n /\ p + n <= 2^64 /\ shadow_bytes m (shad p) (shad p + nshad n) (blockf p n).
#[using="Type"] Lemma shadow_block_unpoisoned : forall m p n, shadow_block m p n -> unpoisoned m p (p + n).
Proof.
intros m p n (AL & P0 & N0 & PN & (A & B & H)). Local Ltac2 Set LiaHints.tbl := fun () => "0060>32622447550.314115623262.11 41557075107.1643089425877.3146270986570.2952574990546.1100000:00>00?00L00_00cS2AL2n02H3S2P0SS2AL2H22n02H3S2AL2H12H22H32H82H9S2PN".
split; [lia|]. split; [lia|].
intros G H0 H1 H2. rewrite nshad_div, shad_div in *.
assert (R : ASHOFF + p / 8 <= ASHOFF + G < ASHOFF + p / 8 + (n + 7) / 8) by (Z.div_mod_to_equations; lia).
exists (Z_to_bv 8 (blockf p n (ASHOFF + G))). split. { apply H. exact R. }
unfold blockf. rewrite shad_div. cbn zeta.
replace (ASHOFF + G - (ASHOFF + p / 8)) with (G - p / 8) by lia.
destruct (Z.leb_spec0 (8 * (G - p / 8) + 8) n).
- left. apply sval_zero.
- right. rewrite sval_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ov_read_of_bytes_at : forall m a bs,
bytes_at segs m a bs -> ov_read_bytes segs m (wa a) (length bs) = Some bs.
Proof.
intros m a bs H. Local Ltac2 Set LiaHints.tbl := fun () => "0010<1610020649.5000001S".
pose proof (bytes_at_ov_read segs m a bs 0 (length bs) H ltac:(lia)) as R.
rewrite Z.add_0_r in R. cbn [skipn] in R. rewrite firstn_all in R. exact R.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ov_read1_of_byte : forall m s b, 0 <= s -> s + 1 <= 2^64 -> m (wa s) = Some b ->
ov_read_bytes segs m (wa s) 1 = Some [b].
Proof.
intros m s b A B H. apply (ov_read_of_bytes_at m s [b]). Local Ltac2 Set LiaHints.tbl := fun () => "0030=11863645839.725602808726.751388266601.900000300600:S1AS1BS2Hi".
split; [lia|]. split; [cbn; lia|].
intros [|i] Hi; cbn in Hi; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. unfold mrd. rewrite H. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ov_read1_of_shadow_bytes : forall m s1 s2 f s,
shadow_bytes m s1 s2 f -> s1 <= s < s2 -> ov_read_bytes segs m (wa s) 1 = Some [Z_to_bv 8 (f s)].
Proof. intros m s1 s2 f s (A & B & H) Hs. Local Ltac2 Set LiaHints.tbl := fun () => "0030>11865735282.1038621375894.1053701529329.1000000600<00@S1A2HsS1B2HsS2Hs".
apply ov_read1_of_byte; [lia|lia|]. apply H. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ov_read8_of_shadow_bytes : forall m s1 s2 f s,
shadow_bytes m s1 s2 f -> s1 <= s -> s + 8 <= s2 -> ov_read_bytes segs m (wa s) 8 = Some (shadow_list s 8 f).
Proof.
intros m s1 s2 f s SB H1 H2.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>31962213041.1043853320889.9 000001002SS".
pose proof (bytes_at_of_shadow_bytes m s (s + 8) f (shadow_bytes_sub m s1 s2 f s (s + 8) SB H1 H2) ltac:(lia)) as BA.
replace (s + 8 - s) with 8 in BA by lia.
rewrite <- (shadow_list_length s 8 f) at 1. apply ov_read_of_bytes_at. exact BA.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ov_read8_zero : forall m s1 s2 f s,
shadow_bytes m s1 s2 f -> s1 <= s -> s + 8 <= s2 -> (forall s', s <= s' < s + 8 -> Z_to_bv 8 (f s') = Z_to_bv 8 0) ->
ov_read_bytes segs m (wa s) 8 = Some (le8 (Z_to_bv 64 0)).
Proof.
intros m s1 s2 f s SB H1 H2 E.
pose proof (shadow_bytes_ext m s (s + 8) f (fun _ => 0) (shadow_bytes_sub m s1 s2 f s (s + 8) SB H1 H2) E) as SB0.
rewrite (ov_read8_of_shadow_bytes m s (s + 8) (fun _ => 0) s SB0) by lia.
reflexivity.
Qed.
#[using="Type"] Lemma ov_read8_of_wr_at : forall m s, wr_at segs m s 8 -> no_image s (s + 8) ->
exists w : word, ov_read_bytes segs m (wa s) 8 = Some (le8 w).
Proof.
intros m s W NI. destruct (rw_cells_C8_of_wr_at m s W NI) as [w R]. exists w.
pose proof (rw_cells_read segs m s [C8 w] 0 (C8 w) R eq_refl) as RD. rewrite Z.add_0_r in RD. exact RD.
Qed.
#[using="Type"] Lemma unpoisoned_full_rd : forall m lo hi c,
unpoisoned m lo hi -> shad lo <= c -> 8 * (c - ASHOFF) + 8 <= hi ->
ov_read_bytes segs m (wa c) 1 = Some [Z_to_bv 8 0].
Proof.
intros m lo hi c U H1 H2. pose proof U as (A & B & _). rewrite shad_div in H1.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>1501555492.17 26346168444.1035671695878.17472155874.17  68390435360.1700000600700;00D00OS2H21BSS2H2S2H11H2H0S2H11A1H2H0".
apply ov_read1_of_byte; [unfold ASHOFF in *; Z.div_mod_to_equations; lia | unfold ASHOFF in *; Z.div_mod_to_equations; lia |].
replace c with (ASHOFF + (c - ASHOFF)) at 1 by lia.
apply (unpoisoned_full m lo hi (c - ASHOFF) U); Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unpoisoned_check_rd : forall m lo hi a N,
unpoisoned m lo hi -> lo <= a -> a + N <= hi -> 1 <= N -> a mod 8 + N <= 8 ->
exists b, ov_read_bytes segs m (wa (shad a)) 1 = Some [b] /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + N - 1 < sval b)).
Proof.
intros m lo hi a N U H1 H2 H3 H4. destruct (unpoisoned_check m lo hi a N U H1 H2 H3 H4) as (b & R & Hb).
exists b. split; [|exact Hb].
pose proof (rw_cells_read segs m (shad a) [C1 b] 0 (C1 b) R eq_refl) as RD. rewrite Z.add_0_r in RD. exact RD.
Qed.
#[using="Type"] Lemma wr_at_sub : forall m a n a' n', wr_at segs m a n -> a <= a' -> a' + n' <= a + n -> wr_at segs m a' n'.
Proof. intros m a n a' n' (A & B & H) H1 H2. Local Ltac2 Set LiaHints.tbl := fun () => "0040>1849204920.13 42667250172.134856259436.11 48935769329.1100000100;00A00GSS2H12H22HiS1B2H2S1A2H1".
split; [lia|]. split; [lia|]. intros i Hi. replace (a' + i) with (a + (a' + i - a)) by lia. apply H. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shadow_probe8 : forall m RLO RHI x,
wr_at segs m (shad RLO) (shad RHI - shad RLO) -> no_image (shad RLO) (shad RHI) ->
RLO mod 64 = 0 -> RHI mod 64 = 0 -> 0 <= RLO -> RLO <= x < RHI -> RHI <= 2^64 ->
exists w : word, ov_read_bytes segs m (wa (ASHOFF + Z.shiftr x 3 - (ASHOFF + Z.shiftr x 3) mod 8)) 8 = Some (le8 w).
Proof.
intros m RLO RHI x W NI A1 A2 A0 Hx HR.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>29784462332.1241965600285.5450451367165.1657083738316.1458150493105.1400000100]00d00h00lSS2A12A22Hx1H2H02H42H52H93H103H143H153H193H24S2HP2HzS2HPS2HP".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite !shad_div in W, NI. unfold ASHOFF in *.
set (P := 2147450880 + x / 8 - (2147450880 + x / 8) mod 8).
assert (HP : 2147450880 + RLO / 8 <= P /\ P + 8 <= 2147450880 + RHI / 8) by (subst P; Z.div_mod_to_equations; lia).
apply ov_read8_of_wr_at.
- eapply wr_at_sub; [exact W| lia | lia].
- intros z Hz. apply NI. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unpoisoned_of_zero : forall m s1 s2 f lo hi,
shadow_bytes m s1 s2 f -> (forall s, s1 <= s < s2 -> Z_to_bv 8 (f s) = Z_to_bv 8 0) ->
s1 <= shad lo -> shad (hi - 1) + 1 <= s2 -> 0 <= lo -> hi <= 2^64 ->
unpoisoned m lo hi.
Proof.
intros m s1 s2 f lo hi (A & B & H) Z0 H1 H2 L0 Hh. Local Ltac2 Set LiaHints.tbl := fun () => "0040>29430566067.1548347288418.2048351912899.3352367201392.1500000400700P00TS2L0S1RS2H12H22G12G22H02H32H72H8S2Hh".
split; [lia|]. split; [lia|].
intros G G0 G1 G2. rewrite !shad_div in *. unfold ASHOFF in *.
assert (R : s1 <= 2147450880 + G < s2) by (Z.div_mod_to_equations; lia).
exists (Z_to_bv 8 0). split. { rewrite <- (Z0 (2147450880 + G)) by lia. apply H. lia. }
left. apply sval_zero.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithSegs.
