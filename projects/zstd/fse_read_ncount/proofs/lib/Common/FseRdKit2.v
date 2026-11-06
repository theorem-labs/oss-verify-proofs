(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit FseRdKit.
Import ListNotations.
Open Scope Z_scope.
Lemma land_mod_pow2 : forall a b n, 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof.
intros a b n Hn. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z_lt_le_dec i n).
- Local Ltac2 Set LiaHints.tbl := fun () => "0020=26078223342.753766211437.7000006009S2Hn1lS1l".
rewrite !Z.mod_pow2_bits_low by lia. apply Z.land_spec.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma lor_mod_pow2 : forall a b n, 0 <= n -> (Z.lor a b) mod 2^n = Z.lor (a mod 2^n) (b mod 2^n).
Proof.
intros a b n Hn. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
destruct (Z_lt_le_dec i n).
- Local Ltac2 Set LiaHints.tbl := fun () => "0020=26078223342.753766211437.7000006009S2Hn1lS1l".
rewrite !Z.mod_pow2_bits_low by lia. apply Z.lor_spec.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land_compl : forall a m, 0 <= m -> 0 <= a < 2^m -> Z.land a (2^m - 1 - a) = 0.
Proof.
intros a m Hm Ha.
assert (E : 2^m - 1 - a = Z.ldiff (Z.ones m) a).
{ rewrite <- Z.sub_nocarry_ldiff.
- rewrite Z.ones_equiv. Local Ltac2 Set LiaHints.tbl := fun () => "0040=16834832610.732043624750.732216090041.732482879922.400000600<00@00AS2Hm1lS2Hi1lS2HaS".
lia.
- apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
destruct (Z_lt_le_dec i m).
+ rewrite Z.ones_spec_low by lia. apply andb_false_r.
+ rewrite (testbit_high_false a m i) by lia. reflexivity. }
rewrite E. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0.
destruct (Z.testbit a i); cbn; [apply andb_false_r| reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma lowbit_land : forall (f : nat) v, 0 < v < 2^(Z.of_nat f) -> Z.land v (2^(Z.of_nat f) - v) = 2^(ctz_aux f v).
Proof.
induction f as [|f IH]; intros v Hv.
- cbn in Hv. Local Ltac2 Set LiaHints.tbl := fun () => "00A0>18729815015.9 25232601564.2 40825696453.1241252081172.1241992069702.104232765486.9  48361995550.8 48368632352.1248842276258.1050194598317.9 53752074787.12590128110.12  592265110.4   592325745.6   59724224524.9 6757635357.9  6758013062.10 00000100500;00A00B00C00J00M00P00Q00R00S00T00U00V00W00XSS2HvS2Hi1NS2Hi1NSSS2Hv2DOS1QS1HSSSSSSSS".
lia.
- rewrite Nat2Z.inj_succ in *. unfold Z.succ in *. rewrite (pow2_S (Z.of_nat f)) in * by lia.
cbn [ctz_aux].
pose proof (Z.div2_odd v) as DO. set (a := Z.div2 v) in *.
assert (P0 : 0 < 2 ^ Z.of_nat f) by (apply pow2_pos; lia).
destruct (Z.odd v) eqn:EO; cbn [Z.b2z] in DO.
+
assert (Q : 0 <= a < 2 ^ Z.of_nat f) by lia.
rewrite DO at 1 2.
replace (2 * 2 ^ Z.of_nat f - (2 * a + 1)) with (2 * (2 ^ Z.of_nat f - 1 - a) + 1) by lia.
change (2 ^ 0) with 1.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.eq_dec i 0) as [->|N].
* rewrite !Z.testbit_odd_0. reflexivity.
* replace i with (Z.succ (i - 1)) by lia. rewrite !Z.testbit_odd_succ by lia.
rewrite <- Z.land_spec, (land_compl a (Z.of_nat f)) by lia. rewrite Z.bits_0.
change 1 with (2 * 0 + 1). rewrite Z.testbit_odd_succ by lia. rewrite Z.bits_0. reflexivity.
+ rewrite Z.add_0_r in DO.
assert (Q : 0 < a < 2 ^ Z.of_nat f) by lia.
rewrite DO at 1 2.
replace (2 * 2 ^ Z.of_nat f - 2 * a) with (2 * (2 ^ Z.of_nat f - a)) by lia.
replace (2 * a) with (Z.shiftl a 1) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^1) with 2; lia).
replace (2 * (2 ^ Z.of_nat f - a)) with (Z.shiftl (2 ^ Z.of_nat f - a) 1) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^1) with 2; lia).
rewrite <- Z.shiftl_land. rewrite (IH a Q). rewrite Z.shiftl_mul_pow2 by lia.
pose proof (ctz_aux_le f a). rewrite Z.pow_add_r by lia. change (2^1) with 2. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition ctzv (bs : Z) : Z := ctz_aux 32 (Z.lor (not32 bs) (2^31)).
Definition db_idx (k : Z) : Z := ((2^k * 125613361) mod 2^32) / 2^27.
Definition DB_TABLE : list Z :=
[0; 1; 28; 2; 29; 14; 24; 3; 30; 22; 20; 15; 25; 17; 4; 8; 31; 27; 13; 23; 21; 19; 16; 7; 26; 12; 18; 6; 11; 5; 10; 9].
Lemma db_table_ok_range : forall k, 0 <= k < 32 -> 0 <= db_idx k < 32.
Proof.
intros k Hk.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=3673095980.4 59064484231.200000700;S2H02H1S2Hk".
pose proof (brute_range (fun k0 => (0 <=? db_idx k0) && (db_idx k0 <? 32)) 0 32 ltac:(vm_compute; reflexivity) k ltac:(lia)) as H.
cbv beta in H. apply andb_true_iff in H. destruct H as [H0 H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ctzv_arg_range : forall bs, 0 <= bs < 2^32 -> 0 < Z.lor (not32 bs) (2^31) < 2^32.
Proof. intros bs Hb. Local Ltac2 Set LiaHints.tbl := fun () => "0010=27593707945.2000001S".
exact (proj2 (repeats_arg_mod bs 0 Hb ltac:(lia))). Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ctzv_lowbit : forall bs, 0 <= bs < 2^32 ->
Z.land (Z.lor (not32 bs) (2^31)) (2^32 - Z.lor (not32 bs) (2^31)) = 2^(ctzv bs).
Proof. intros bs Hb. exact (lowbit_land 32 _ (ctzv_arg_range bs Hb)). Qed.
Lemma ctzv_range : forall bs, 0 <= bs < 2^32 -> 0 <= ctzv bs <= 31.
Proof.
intros bs Hb. pose proof (ctz_aux_le 32 (Z.lor (not32 bs) (2^31))) as L. fold (ctzv bs) in L. Local Ltac2 Set LiaHints.tbl := fun () => "0060=16046348693.544021460374.74777319650.5 61505652591.668393056305.39544766530.7 00000500800=00B00E00HS1L1RS1LS1L1RS1L1BS1LS1L".
split; [lia|].
pose proof (ctzv_arg_range bs Hb) as R. pose proof (ctzv_lowbit bs Hb) as E.
pose proof (land_lt_pow2 (Z.lor (not32 bs) (2^31)) (2^32 - Z.lor (not32 bs) (2^31)) 32 ltac:(lia) ltac:(lia)) as B.
rewrite E in B. destruct B as [_ B]. apply Z.pow_lt_mono_r_iff in B; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma repeats_of_ctzv : forall bs, 0 <= bs < 2^32 -> repeats_of bs = Ok (ctzv bs / 2).
Proof.
intros bs Hb. unfold repeats_of, ctz32. pose proof (ctzv_arg_range bs Hb) as R.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=10863850115.316045970176.3000003006S1RS1R".
rewrite u32_id by lia. replace (Z.lor (not32 bs) (2 ^ 31) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ctz_index_form : forall bs, 0 <= bs < 2^32 ->
bv_swrap 32
(bv_wrap 32
((Z.land (Z.lor (Z.lxor (bv_swrap 32 bs mod 18446744073709551616) 18446744073709551615) 18446744071562067968)
(bv_swrap 32 (0 - Z.lor (Z.lxor (bv_swrap 32 bs mod 18446744073709551616) 18446744073709551615) 18446744071562067968)
mod 18446744073709551616) * 125613361) mod 18446744073709551616) ≫ 27)
= db_idx (ctzv bs).
Proof.
intros bs Hb.
set (X := bv_swrap 32 bs mod 18446744073709551616).
Local Ltac2 Set LiaHints.tbl := fun () => "00A0>16039926544.8 25842128210.9 25851511130.8 38715565820.9 38715879826.1338715882505.6 38948406459.2 42470600790.7 44015118492.1144015334120.6 47754421023.9 5259880692.6  53395489667.1353681669037.9 62186928258.1366095883697.148324888622.3  00000400500900:00;00<00=00>00?00@00A00E00F00J00N00Q00US2MBSS2DMSSSSSSSSS2RXSS2RvS2RkS1HS2Hb".
assert (RX : 0 <= X < 2^64) by (subst X; apply Z.mod_pos_bound; lia).
assert (EX : X mod 2^32 = bs) by (subst X; apply swrap32_u32_mod32; lia).
set (A := Z.lor (Z.lxor X 18446744073709551615) 18446744071562067968).
set (v := Z.lor (not32 bs) (2^31)).
pose proof (ctzv_arg_range bs Hb) as Rv. fold v in Rv.
assert (EA : A mod 2^32 = v).
{ subst A v. rewrite lor_mod_pow2 by lia. f_equal.
rewrite zb_lxor_ones by lia. unfold not32. rewrite <- EX.
pose proof (Z.div_mod X (2^32) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound X (2^32) ltac:(lia)) as MB.
replace (18446744073709551615 - X) with ((2^32 - 1 - X mod 2^32) + (2^32 - 1 - X / 2^32) * 2^32) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
set (B := bv_swrap 32 (0 - A) mod 18446744073709551616).
assert (EB : B mod 2^32 = 2^32 - v).
{ subst B. change 18446744073709551616 with (2^64).
rewrite (Z.mod_mod_divide _ (2^64) (2^32)) by (exists (2^32); reflexivity).
rewrite swrap32_eq. change 4294967296 with (2^32). change 2147483648 with (2^31).
rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
replace (0 - A + 2^31 - 2^31) with (0 - A) by lia.
rewrite Zminus_mod, EA, Z.mod_0_l by lia.
replace (0 - v) with ((2^32 - v) + (-1) * 2^32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (EY : (Z.land A B) mod 2^32 = 2^(ctzv bs)).
{ rewrite land_mod_pow2 by lia. rewrite EA, EB. apply ctzv_lowbit. exact Hb. }
pose proof (ctzv_range bs Hb) as Rk.
rewrite wrap32_eq. change 4294967296 with (2^32). change 18446744073709551616 with (2^64).
rewrite (Z.mod_mod_divide _ (2^64) (2^32)) by (exists (2^32); reflexivity).
rewrite Zmult_mod, EY. rewrite <- Zmult_mod_idemp_r. rewrite Z.mod_mod by lia. rewrite Zmult_mod_idemp_r.
rewrite Z.shiftr_div_pow2 by lia. fold (db_idx (ctzv bs)).
apply swrap32_small. pose proof (db_table_ok_range (ctzv bs) ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma db_table_ok : forall k, 0 <= k < 32 -> 0 <= db_idx k < 32 /\ nth (Z.to_nat (db_idx k)) DB_TABLE 0 = k.
Proof.
intros k Hk.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=59064484231.2000004S2Hk".
pose proof (brute_range (fun k0 => (0 <=? db_idx k0) && (db_idx k0 <? 32) && (nth (Z.to_nat (db_idx k0)) DB_TABLE 0 =? k0)) 0 32
ltac:(vm_compute; reflexivity) k ltac:(lia)) as H.
cbv beta in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma readLE32_inv : forall buf ip w, readLE32 buf ip = Ok w -> 0 <= ip /\ ip + 4 <= zlen buf /\ w = le32 buf ip.
Proof.
intros buf ip w E. unfold readLE32, FseNCount.Zlength in E.
destruct ((0 <=? ip) && (ip + 4 <=? zlen buf)) eqn:B; [|discriminate].
apply andb_true_iff in B. destruct B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
injection E as <-. unfold le32. auto.
Qed.
Lemma shr32_inv : forall w n v, shr32 w n = Ok v -> 0 <= n < 32 /\ v = w / 2^n.
Proof.
intros w n v E. unfold shr32 in E. destruct ((0 <=? n) && (n <? 32)) eqn:B; [|discriminate].
apply andb_true_iff in B. destruct B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
injection E as <-. auto.
Qed.
Lemma shr_range : forall w n, 0 <= w < 2^32 -> 0 <= n -> 0 <= w / 2^n < 2^32.
Proof.
intros w n Hw Hn. pose proof (pow2_pos n Hn). Local Ltac2 Set LiaHints.tbl := fun () => "0020=60746310587.56966288195.5 000004007S2HwS1H".
split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ctz_masks : forall k, 0 <= k < 32 -> k ≫ 1 = k / 2 /\ Z.land k 254 = 2 * (k / 2) /\ Z.land k 30 = 2 * (k / 2).
Proof.
intros k Hk.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=59064484231.2000004S2Hk".
pose proof (brute_range (fun k0 => (k0 ≫ 1 =? k0 / 2) && (Z.land k0 254 =? 2 * (k0 / 2)) && (Z.land k0 30 =? 2 * (k0 / 2))) 0 32
ltac:(vm_compute; reflexivity) k ltac:(lia)) as H.
cbv beta in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wrap32_swrap32_u32 : forall bs, 0 <= bs < 2^32 -> bv_wrap 32 (bv_swrap 32 bs mod 18446744073709551616) = bs.
Proof. intros bs Hb. rewrite wrap32_eq. change 4294967296 with (2^32). apply swrap32_u32_mod32. exact Hb. Qed.
Lemma le2_zero : le2 (Z_to_bv 64 0) = [Z_to_bv 8 0; Z_to_bv 8 0].
Proof. reflexivity. Qed.
Lemma u16s_zero_prefix : forall n (l : list Z), (n <= length l)%nat ->
repeat (Z_to_bv 8 0) (2 * n) ++ skipn (2 * n) (u16s (map (Z_to_bv 64) l)) = u16s (map (Z_to_bv 64) (zero_prefix n l)).
Proof.
induction n as [|n IH]; intros l Hl.
- cbn [Nat.mul repeat app skipn zero_prefix]. destruct l; reflexivity.
- Local Ltac2 Set LiaHints.tbl := fun () => "0070>29750822426.8 41773580864.5 46619615367.3 54071794387.1054071794387.6 54071794387.7 54071794387.8 00000400800<00C00J00Q00RS2HlS2HlS2HlS2Hl2L2S2Hl2L2S2Hl2L2F".
destruct l as [|a l]; [cbn in Hl; lia|].
replace (2 * S n)%nat with (S (S (2 * n))) by lia.
cbn [repeat app zero_prefix map u16s]. rewrite le2_zero. cbn [app].
pose proof (length_le2 (Z_to_bv 64 a)) as L2.
destruct (le2 (Z_to_bv 64 a)) as [|b0 [|b1 [|b2 r]]]; cbn in L2; try lia.
cbn [app skipn]. rewrite IH by (cbn in Hl; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold sx32. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0020=16435405267.238557618280.2000004008S2HzS2Hz".
rewrite unsigned_lit by lia. apply swrap32_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rd_s0 (buf : list Z) (msv1 : Z) (nc0 : list Z) : rstate :=
let w := le32 buf 0 in let x := Z.land w 15 in
FseNCount.mkR (zero_prefix (Z.to_nat msv1) nc0) 0 (w / 2^4) 4 0 (2^(x + 5) + 1) (2^(x + 5)) (x + 5 + 1) false.
Lemma read_body8_inv : forall buf msv1 nc0 rt msv tlr n, 8 <= zlen buf ->
read_ncount_body8 buf msv1 nc0 = Ok (rt, msv, tlr, n) ->
msv1 <= zlen nc0 /\ Z.land (le32 buf 0) 15 <= 10 /\ tlr = Z.land (le32 buf 0) 15 + 5 /\
exists sF, rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 nc0) = Ok sF
/\ r_remaining sF = 1 /\ r_charnum sF <= msv1 /\ r_bitCount sF <= 32
/\ rt = r_nc sF /\ msv = r_charnum sF - 1 /\ n = r_ip sF + (r_bitCount sF + 7) / 8.
Proof.
intros buf msv1 nc0 rt msv tlr n H8 E. unfold read_ncount_body8, assert in E.
destruct (Z.leb_spec msv1 (FseNCount.Zlength nc0)) as [L|L]; cbv iota in E; cbn [bind] in E. 2:{ discriminate E. }
Local Ltac2 Set LiaHints.tbl := fun () => "0080>14398433119.1415043098686.1029784301659.1437271517807.1348501441833.1351002677066.1060750635865.1265504359324.1100000300400500800<00@00A00BS1BSSS1BS2X0S2H8SS".
rewrite (readLE32_le32 buf 0) in E by lia. cbn [bind] in E.
unfold FSE_MIN_TABLELOG, FSE_TABLELOG_ABSOLUTE_MAX in E.
set (x := Z.land (le32 buf 0) 15) in *.
destruct (Z.ltb_spec 15 (x + 5)) as [B|B]; cbv iota in E; [discriminate E|].
rewrite shr32_ok in E by lia. cbn [bind] in E.
assert (X0 : 0 <= x) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
replace ((0 <=? x + 5) && (x + 5 <? 31)) with true in E by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [bind] in E.
assert (ES0 : rd_s0 buf msv1 nc0 = FseNCount.mkR (zero_prefix (Z.to_nat msv1) nc0) 0 (le32 buf 0 / 2 ^ 4) 4 0 (2 ^ (x + 5) + 1) (2 ^ (x + 5)) (x + 5 + 1) false)
by reflexivity.
rewrite <- ES0 in E.
destruct (rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 nc0)) as [sF| | |] eqn:RL; cbn [bind] in E; try discriminate E.
destruct (Z.eqb_spec (r_remaining sF) 1) as [E1|N1]; cbn [negb] in E; cbv iota in E; [|discriminate E].
destruct (Z.ltb_spec msv1 (r_charnum sF)) as [B2|B2]; cbv iota in E; [discriminate E|].
destruct (Z.ltb_spec 32 (r_bitCount sF)) as [B3|B3]; cbv iota in E; [discriminate E|].
injection E as <- <- <- <-.
unfold FseNCount.Zlength in L. split; [exact L|]. split; [lia|]. split; [reflexivity|].
exists sF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rd_s0_inv : forall buf msv1 nc0, all_bytes buf -> 8 <= zlen buf -> 1 <= msv1 <= zlen nc0 -> Z.land (le32 buf 0) 15 <= 10 ->
CTL msv1 nc0 (Z.land (le32 buf 0) 15 + 5) (rd_s0 buf msv1 nc0) /\ POS buf (rd_s0 buf msv1 nc0) /\ r_bitCount (rd_s0 buf msv1 nc0) < 32.
Proof.
intros buf msv1 nc0 HB H8 Hm HX. unfold rd_s0. cbv zeta.
set (x := Z.land (le32 buf 0) 15) in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00H0>10969410027.1215043033658.1315164382823.1215661606428.1223084946773.1333164461214.1337687684636.1238889411643.1238981499111.1240818989526.1341415861068.1147006930252.1448501617024.1051002611022.1351218409354.1351813034855.1153879186035.1455754769198.1256315339017.1457129067197.1258827432013.1263311639564.1364140522160.1265502428806.7 00000100200600:00=00>00?00C00D00E00F00M00Q00U00V00Z00a00b00e00i00j00m011012SSS2X0S2P5S1HSSS2RWSSSS2Hm2HiS2X0S2H8SS2X0S2Hm2HiSS1HS2HmSS1HS2RWS".
assert (X0 : 0 <= x) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
pose proof (le32_range buf 0 HB) as RW.
assert (P2 : 2 ^ (x + 5 + 1) = 2 * 2 ^ (x + 5)) by (apply pow2_S; lia).
assert (P5 : 32 <= 2 ^ (x + 5)) by (change 32 with (2^5); apply Z.pow_le_mono_r; lia).
split; [|split].
- unfold CTL. cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0].
split; [apply zero_prefix_length|]. split; [lia|].
split. { intros i Hi. unfold Znth. rewrite zero_prefix_nth. replace (Z.to_nat i <? Z.to_nat msv1)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
split. { intros i Hi. unfold Znth. rewrite zero_prefix_nth. replace (Z.to_nat i <? Z.to_nat msv1)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity. }
split. { f_equal. lia. } split; [lia|]. split; [lia|]. split; [lia|].
intros _. split; [intros; lia|]. unfold pws. change (Z.to_nat 0) with 0%nat. rewrite firstn_O. cbn [wsum]. lia.
- unfold POS. cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0].
assert (0 <= le32 buf 0 / 2^4 < 2^32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold FseNCount.Zlength. repeat split; lia.
- cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma le32_lbu_raw : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 b3) ≪ 24 mod 18446744073709551616)
(bv_unsigned (Z_to_bv 8 b2) ≪ 16 mod 18446744073709551616))
(Z.lor (bv_unsigned (Z_to_bv 8 b1) ≪ 8 mod 18446744073709551616) (bv_unsigned (Z_to_bv 8 b0)))
= b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3.
Proof.
intros b0 b1 b2 b3 H0 H1 H2 H3.
rewrite !byte_lit by assumption. Local Ltac2 Set LiaHints.tbl := fun () => "00>0=16669400259.82250401347.8 23363119011.825160791242.840002976247.841891548331.846306201989.847595667734.852412116923.853040169880.863368316331.865502414891.866801051605.86974761201.8 00000400800<00=00A00B00F00G00N00O00P00Q00U00YS2H2S2H2S2H3SS2H0SS2H3SS2H02H1SSSS2H1S2H1".
rewrite !Z.shiftl_mul_pow2 by lia.
change 18446744073709551616 with (2^64).
rewrite (Z.mod_small (b3 * 2^24)) by lia. rewrite (Z.mod_small (b2 * 2^16)) by lia. rewrite (Z.mod_small (b1 * 2^8)) by lia.
rewrite (Z.lor_comm (b1 * 2^8) b0). rewrite (lor_add_disjoint b0 (b1 * 2^8) 8) by (try lia; apply Z.mod_mul; lia).
rewrite (Z.lor_comm (b3 * 2^24) (b2 * 2^16)).
rewrite (lor_add_disjoint (b2 * 2^16) (b3 * 2^24) 24) by (try lia; apply Z.mod_mul; lia).
rewrite Z.lor_comm. rewrite (lor_add_disjoint (b0 + b1 * 2^8) (b2 * 2^16 + b3 * 2^24) 16).
- lia.
- lia.
- lia.
- replace (b2 * 2^16 + b3 * 2^24) with ((b2 + b3 * 2^8) * 2^16) by lia. apply Z.mod_mul. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
