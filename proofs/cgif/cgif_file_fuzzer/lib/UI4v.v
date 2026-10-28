(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import Utf8.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0r UI1w UN3b UN3c UI55.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 UI5c YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI01 YI6c YI67 UN0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI02 YI03 YI0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI4l YI5a UI2v UI5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI3w UIZe UIZc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_ok_add_region : forall segs E ss ms r,
st_ok segs E ss ms -> region_wf r = true -> region_ok segs E (ms_mem ms) r -> all_disjoint E r (ss_mem ss) ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof using.
intros segs E ss ms r (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hrwf Hr Hd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [cbn; rewrite Hrwf, Hwf; reflexivity|]. split; [constructor; assumption|]. split; assumption.
Qed.
Lemma st_ok_widen_head : forall segs E ss ms n lo hi whi cs rest lo',
st_ok segs E ss ms ->
ss_mem ss = YP09.mkRegion (Some n) lo hi lo whi cs :: rest ->
lo' <= lo ->
(forall a, bv_unsigned (ew E n) + lo' <= a < bv_unsigned (ew E n) + lo -> writable_at segs (ms_mem ms) a) ->
0 <= bv_unsigned (ew E n) + lo' ->
all_disjoint E (YP09.mkRegion (Some n) lo' hi lo' whi cs) rest ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (YP09.mkRegion (Some n) lo' hi lo' whi cs :: rest) (ss_resv ss) (ss_facts ss)) ms.
Proof using.
intros segs E ss ms n lo hi whi cs rest lo' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm Hlo Hw Hpos Hd.
rewrite Hm in Hwf, Hok, Hpd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
cbn in Hwf. apply andb_prop in Hwf as [Hr Hwf].
inversion Hok as [|r0 rs0 Hr0 Hrs]; subst.
split; [|split].
- cbn. rewrite Hwf. unfold region_wf in Hr |- *. cbn [r_lo r_hi r_wlo r_whi r_chunks] in *.
apply andb_prop in Hr as [Hr Hci]. apply andb_prop in Hr as [Hr1 Hr2].
apply Z.leb_le in Hr1.
replace (lo' <=? hi) with true by (symmetry; apply Z.leb_le; lia).
assert (Hw2 : (whi <=? lo') || ((lo' <=? lo') && (whi <=? hi)) = true).
{ apply Bool.orb_true_iff in Hr2. apply Bool.orb_true_iff.
destruct Hr2 as [Hr2|Hr2]; [apply Z.leb_le in Hr2 | apply andb_prop in Hr2 as [_ Hr2]; apply Z.leb_le in Hr2].
- destruct (Z_le_gt_dec whi lo'); [left; apply Z.leb_le; lia | right; apply andb_true_intro; split; apply Z.leb_le; lia].
- right; apply andb_true_intro; split; apply Z.leb_le; lia. }
rewrite Hw2. cbn [andb]. rewrite Bool.andb_true_r.
apply (proj2 (forallb_forall _ _)). intros c Hc. pose proof (proj1 (forallb_forall _ _) Hci c Hc) as Hcc.
unfold chunk_inside in Hcc |- *. cbn [r_lo r_hi] in *.
apply andb_prop in Hcc as [Hcc Hc3]. apply andb_prop in Hcc as [Hc1 Hc2]. apply Z.leb_le in Hc1.
rewrite Hc2, Hc3. replace (lo' <=? c_off c) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- constructor; [|exact Hrs]. unfold region_ok in Hr0 |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in *.
destruct Hr0 as (Ha & Hb & Hc & Hd'). split; [lia|]. split; [exact Hb|]. split; [|exact Hd'].
intros o Ho. destruct (Z_lt_le_dec o lo); [apply Hw; lia | apply Hc; lia].
- cbn. split; [exact Hd | exact (proj2 Hpd)].
Qed.
Lemma st_ok_swap01 : forall segs E ss ms r0 r1 rest,
st_ok segs E ss ms -> ss_mem ss = r0 :: r1 :: rest ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (r1 :: r0 :: rest) (ss_resv ss) (ss_facts ss)) ms.
Proof using.
intros segs E ss ms r0 r1 rest (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm.
rewrite Hm in Hwf, Hok, Hpd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
cbn in Hwf. apply andb_prop in Hwf as [Ha Hwf]. apply andb_prop in Hwf as [Hb Hwf].
inversion Hok as [|x l Hr0 Hok1]; subst. inversion Hok1 as [|y l' Hr1 Hok2]; subst.
cbn in Hpd. destruct Hpd as ((H01 & H0r) & H1r & Hr).
split; [cbn; rewrite Ha, Hb, Hwf; reflexivity|].
split. { constructor. exact Hr1. constructor. exact Hr0. exact Hok2. }
cbn. repeat split; try assumption. unfold extent_disjoint in *. lia.
Qed.
Lemma obj_at_copy : forall segs mem mem' a b lay vals sz,
obj_at segs mem a lay vals -> lay_inside lay sz = true ->
(forall i, 0 <= i < sz -> mbyte segs mem' (b + i) = mbyte segs mem (a + i)) ->
obj_at segs mem' b lay vals.
Proof using.
intros segs mem mem' a b lay. induction lay as [|f lay IH]; intros [|v vals] sz H Hin Heq; cbn in *; try tauto.
unfold lay_inside in Hin. cbn [forallb] in Hin. apply andb_prop in Hin as [Hf Hin].
apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
destruct H as [[Hv Hr] H]. split.
- split; [|exact Hr]. intros k Hk. pose proof (N_nat_Z (snd f)).
replace (b + fst f + Z.of_nat k) with (b + (fst f + Z.of_nat k)) by lia. rewrite Heq by lia.
replace (a + (fst f + Z.of_nat k)) with (a + fst f + Z.of_nat k) by lia. apply Hv. exact Hk.
- eapply IH; [exact H | exact Hin | exact Heq].
Qed.
Lemma LAY_RawConfig_ok : lay_inside LAY_RawConfig 40 = true /\ lay_widths_ok LAY_RawConfig = true.
Proof using. split; reflexivity. Qed.
Lemma LAY_Raw_ok : lay_inside LAY_Raw RAW_SIZE = true /\ lay_widths_ok LAY_Raw = true.
Proof using. split; reflexivity. Qed.
Lemma Ereg_vals2 : forall regs vals1 vals2 more j v,
nth_error vals2 j = Some v ->
ew (Ereg regs (map (Z_to_bv 64) vals1 ++ (map (Z_to_bv 64) vals2 ++ more))) (32 + (length vals1 + j)) = Z_to_bv 64 v.
Proof using.
intros regs vals1 vals2 more j v Hj. rewrite ew_Ereg_extra.
rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map.
replace (length vals1 + j - length vals1)%nat with j by lia.
assert (Hl : (j < length vals2)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite app_nth1 by (rewrite length_map; exact Hl).
apply (nth_error_nth (map (Z_to_bv 64) vals2) j). apply map_nth_error. exact Hj.
Qed.
Lemma st_ok_pin_reg : forall segs E ss ms (r : reg) z,
st_ok segs E ss ms -> getr (ms_regs ms) r = Z_to_bv 64 z -> bv_eqb r 0 = false ->
st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit z)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof using.
intros segs E ss ms r z HS Hr Hr0. apply st_ok_regs; [exact HS|].
intros rr. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. cbn [sv_denot]. rewrite <- (st_ok_reg segs E ss ms r HS), Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
End h.
Ltac pin_reg HS r z Hval :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
let H2 := fresh "HSp" in
pose proof (st_ok_pin_reg segs E1 ss1 ms1 r z HS ltac:(first [exact Hval | cbn [ms_regs]; exact Hval | cbn [ms_regs]; rewrite Hval; reflexivity]) eq_refl) as H2;
let v := eval vm_compute in (mkSS (ss_pc ss1) (sr_set (ss_regs ss1) r (SLit z)) (ss_mem ss1) (ss_resv ss1) (ss_facts ss1)) in
change (mkSS (ss_pc ss1) (sr_set (ss_regs ss1) r (SLit z)) (ss_mem ss1) (ss_resv ss1) (ss_facts ss1)) with v in H2;
clear HS; rename H2 into HS
end.
Ltac add_fact HS n f :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_fact segs E1 ss1 ms1 n f) in HS;
[ let v := eval vm_compute in (add_atom ss1 n f) in change (add_atom ss1 n f) with v in HS
| unfold afact_ok; cbn [af_lo af_hi af_al2] ]
end.
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma in_wrange_cons : forall E r rs a,
in_wrange E (r :: rs) a <-> (base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r) \/ in_wrange E rs a.
Proof using.
intros E r rs a. unfold in_wrange. split.
- intros (r' & [<-|Hin] & H); [left; exact H | right; exists r'; auto].
- intros [H | (r' & Hin & H)]; [exists r; split; [left; reflexivity | exact H] | exists r'; split; [right; exact Hin | exact H]].
Qed.
Lemma in_wrange_nil : forall E a, ~ in_wrange E [] a.
Proof using. intros E a (r & Hin & _). destruct Hin. Qed.
Lemma pad_ovf_val : forall s K, 0 <= s <= K -> 1 <= K <= 256 ->
bv_wrap 64 (bv_swrap 32 (((((s * 18446744073709551614) mod 2 ^ 64 + 2 * K) mod 2 ^ 64) mod 2 ^ 32)
+ (((0 - (s + - K) mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 32)))
= ((s * 18446744073709551613) mod 2 ^ 64 + 3 * K) mod 2 ^ 64.
Proof using.
intros s K Hs HK.
replace (((s * 18446744073709551614) mod 2 ^ 64 + 2 * K) mod 2 ^ 64) with (2 * (K - s)).
2:{ rewrite Zplus_mod_idemp_l. replace (s * 18446744073709551614 + 2 * K) with (2 * (K - s) + s * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
replace ((0 - (s + - K) mod 2 ^ 64) mod 2 ^ 64) with (K - s).
2:{ rewrite Zminus_mod_idemp_r. rewrite Z.mod_small by lia. lia. }
replace (((s * 18446744073709551613) mod 2 ^ 64 + 3 * K) mod 2 ^ 64) with (3 * (K - s)).
2:{ rewrite Zplus_mod_idemp_l. replace (s * 18446744073709551613 + 3 * K) with (3 * (K - s) + s * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
rewrite !(Z.mod_small _ (2 ^ 32)) by lia.
replace (2 * (K - s) + (K - s)) with (3 * (K - s)) by lia.
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity.
Qed.
Lemma pad_ovf_U : forall E s K c2 cn c3, ew E 38 = Z_to_bv 64 s -> 0 <= s <= K -> 1 <= K <= 256 ->
c2 = 2 * K -> cn = - K -> c3 = 3 * K ->
U E (SAluw ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 38 0) (SLit (-2))) (SLit c2)) (SAlu ALU_SUB (SLit 0) (SOff 38 cn)))
= U E (SAlu ALU_ADD (SMd M_MUL (SOff 38 0) (SLit 18446744073709551613)) (SLit c3)).
Proof using.
intros E s K c2 cn c3 H38 Hs HK -> -> ->.
rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SMd. cbn [zmd_raw].
rewrite !U_SOff, H38, !U_SLit. rewrite unsigned_lit_small by lia. unfold zcanon, M64.
replace ((s + 0) mod 2 ^ 64) with s by (rewrite Z.add_0_r, Z.mod_small by lia; reflexivity).
change ((-2) mod 2 ^ 64) with 18446744073709551614. change (18446744073709551613 mod 2 ^ 64) with 18446744073709551613.
rewrite !(Z.mod_small (2 * K)), !(Z.mod_small (3 * K)) by lia. change (0 mod 2 ^ 64) with 0.
apply pad_ovf_val; lia.
Qed.
Lemma pad_cnt16_U : forall E s K c, ew E 38 = Z_to_bv 64 s -> 0 <= s <= K -> 1 <= K <= 256 -> c = 3 * K * 2 ^ 48 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff 38 0) (SLit 5192296858534827627686071399088128)) (SLit c)) (SLit 48))
= 3 * (K - s).
Proof using.
intros E s K c H38 Hs HK ->.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite U_SOff, H38, !U_SLit. rewrite unsigned_lit_small by lia. unfold zcanon, M64.
replace ((s + 0) mod 2 ^ 64) with s by (rewrite Z.add_0_r, Z.mod_small by lia; reflexivity).
change (5192296858534827627686071399088128 mod 2 ^ 64) with 18445899648779419648.
change (Z.land (48 mod 2 ^ 64) 63) with 48.
rewrite (Z.mod_small (3 * K * 2 ^ 48)) by lia.
replace (((s * 18445899648779419648) mod 2 ^ 64 + 3 * K * 2 ^ 48) mod 2 ^ 64) with (3 * (K - s) * 2 ^ 48).
2:{ rewrite Zplus_mod_idemp_l. replace (s * 18445899648779419648 + 3 * K * 2 ^ 48) with (3 * (K - s) * 2 ^ 48 + s * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. lia.
Qed.
Lemma pad_cnt16_denot : forall E s K c, ew E 38 = Z_to_bv 64 s -> 0 <= s <= K -> 1 <= K <= 256 -> c = 3 * K * 2 ^ 48 ->
sv_denot E (SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff 38 0) (SLit 5192296858534827627686071399088128)) (SLit c)) (SLit 48))
= Z_to_bv 64 (3 * (K - s)).
Proof using.
intros E s K c H38 Hs HK Hc. rewrite denot_lit_U. f_equal. exact (pad_cnt16_U E s K c H38 Hs HK Hc).
Qed.
Lemma byte_u16 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 -> bv_unsigned (sv_denot E (SOff n 0)) mod 256 = v mod 256.
Proof using.
intros E n v Hn Hv. change (U E (SOff n 0) mod 256 = v mod 256). rewrite (U_atom E n v Hn) by lia. reflexivity.
Qed.
Lemma byte_u16_hi : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 ->
bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 8))) mod 256 = (v / 256) mod 256.
Proof using.
intros E n v Hn Hv. change (U E (SAlu ALU_SRL (SOff n 0) (SLit 8)) mod 256 = (v / 256) mod 256).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn), U_SLit by lia. unfold zcanon, M64.
change (Z.land (8 mod 2 ^ 64) 63) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite (Z.mod_small (v / 256)) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). reflexivity.
Qed.
End p.
Ltac ew_strip :=
repeat match goal with
| |- context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | cbv; lia])
end.
Ltac ew_strip_in H :=
repeat match type of H with
| context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) in H by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | cbv; lia])
end.
Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma obj_at_range : forall segs mem a lay vals,
obj_at segs mem a lay vals -> forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ (8 * Z.of_N (snd (nth j lay (0, 8%N)))).
Proof using.
intros segs mem a lay. induction lay as [|f lay IH]; intros [|v' vals] H j v Hj; cbn in H; try tauto; [destruct j; discriminate|].
destruct H as [[_ Hr] H]. destruct j as [|j]; cbn in Hj |- *; [injection Hj as <-; exact Hr | exact (IH vals H j v Hj)].
Qed.
End q.
Ltac agree_tac := first [ apply env_agree_refl | apply env_agree_havoc_ge; [cbv; lia | agree_tac] ].
Section zb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Inductive chunk_bytesZ (E : env) (cs : list YP09.chunk) : Z -> list Z -> Prop :=
| cbz_nil : forall off, chunk_bytesZ E cs off []
| cbz_val : forall off e b bs, In (mkChunk off (CVal 1 e)) cs -> bv_unsigned (sv_denot E e) mod 256 = b ->
  chunk_bytesZ E cs (off + 1) bs -> chunk_bytesZ E cs off (b :: bs)
| cbz_zero : forall off co len bs, In (mkChunk co (CZero len)) cs -> co <= off < co + len ->
  chunk_bytesZ E cs (off + 1) bs -> chunk_bytesZ E cs off (0 :: bs).
Lemma garr8_of_chunk_bytesZ : forall E mem r p a bs off,
region_ok segs E mem r -> r_base r = Some p -> bv_unsigned (ew E p) = a ->
chunk_bytesZ E (r_chunks r) off bs -> garr8 segs mem (a + off) bs.
Proof using.
intros E mem r p a bs off HR Hb Hp HC.
induction HC as [off | off e b bs Hin Hbv HC IH | off co len bs Hin Hr HC IH].
- apply garr8_nil.
- intros [|j] Hj.
+ cbn [nth Z.of_nat]. rewrite Z.add_0_r. split.
* exact (vval_mem_of_chunk_mod segs E mem r p a off 1%N e b HR Hb Hin Hp Hbv ltac:(cbn; lia)).
* rewrite <- Hbv. apply Z.mod_pos_bound. lia.
+ cbn [nth]. cbn [length] in Hj. specialize (IH j ltac:(lia)).
replace (a + off + Z.of_nat (Datatypes.S j)) with (a + (off + 1) + Z.of_nat j) by lia. exact IH.
- intros [|j] Hj.
+ cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [|lia].
intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
pose proof HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
destruct (Hc (off - co) ltac:(cbn [c_len c_val cv_len]; lia)) as (b0 & Hb1 & Hb2).
cbn [cbyte c_val c_off] in Hb1, Hb2. injection Hb1 as <-.
replace (a + off + Z.of_nat 0) with (a + co + (off - co)) by lia. rewrite Hb2. reflexivity.
+ cbn [nth]. cbn [length] in Hj. specialize (IH j ltac:(lia)).
replace (a + off + Z.of_nat (Datatypes.S j)) with (a + (off + 1) + Z.of_nat j) by lia. exact IH.
Qed.
End zb.
Section zc.
Lemma byte_zext16 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 ->
bv_unsigned (sv_denot E (SExt false 16 (SOff n 0))) mod 256 = v mod 256.
Proof using.
intros E n v Hn Hv. change (U E (SExt false 16 (SOff n 0)) mod 256 = v mod 256).
rewrite U_SExt. cbv beta iota. rewrite mod256_zcanon. change (2 ^ Z.of_N 16) with (2 ^ 16). rewrite mod256_mod_pow2 by lia.
rewrite (U_atom E n v Hn) by lia. reflexivity.
Qed.
Lemma byte_zext16_hi : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 ->
bv_unsigned (sv_denot E (SAlu ALU_SRL (SExt false 16 (SOff n 0)) (SLit 8))) mod 256 = (v / 256) mod 256.
Proof using.
intros E n v Hn Hv. change (U E (SAlu ALU_SRL (SExt false 16 (SOff n 0)) (SLit 8)) mod 256 = (v / 256) mod 256).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 8) 63) with 8. rewrite mod256_zcanon, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite U_SExt. cbv beta iota. rewrite (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 16) with 65536. rewrite (Z.mod_small v 65536) by lia.
rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma byte_atom16 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 ->
bv_unsigned (sv_denot E (SOff n 0)) mod 256 = v mod 256.
Proof using.
intros E n v Hn Hv. change (U E (SOff n 0) mod 256 = v mod 256). rewrite (U_atom E n v Hn) by lia. reflexivity.
Qed.
Lemma byte_atom16_hi : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 ->
bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 8))) mod 256 = (v / 256) mod 256.
Proof using.
intros E n v Hn Hv. change (U E (SAlu ALU_SRL (SOff n 0) (SLit 8)) mod 256 = (v / 256) mod 256).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 8) 63) with 8. rewrite mod256_zcanon, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite (U_atom E n v Hn) by lia. reflexivity.
Qed.
Fixpoint memset_cut (b : option nat) (mlo lo : Z) (rs : smem) : smem :=
match rs with
| [] => []
| r :: rs' =>
if obase_eqb (r_base r) b && (r_lo r <? lo) && (mlo <? r_hi r) then
(if lo <? r_hi r then trim_lo r lo :: memset_cut b mlo lo rs' else memset_cut b mlo lo rs')
else r :: memset_cut b mlo lo rs'
end.
Lemma submem_memset_cut : forall b mlo lo rs, submem (memset_cut b mlo lo rs) rs.
Proof using.
intros b mlo lo rs. induction rs as [|r rs IH]; cbn [memset_cut]; [apply submem_nil|].
destruct (obase_eqb (r_base r) b && (r_lo r <? lo) && (mlo <? r_hi r)); [destruct (lo <? r_hi r)|].
- apply submem_keep; [apply subregion_trim_lo | exact IH].
- apply submem_drop. exact IH.
- apply submem_keep; [apply subregion_refl | exact IH].
Qed.
End zc.
Ltac chunk_bytesZ_step byte_tac :=
lazymatch goal with
| |- chunk_bytesZ _ ?cs ?off _ =>
let o := eval vm_compute in off in
first
[ lazymatch cs with
| context [mkChunk o (CVal 1 ?e)] => eapply (cbz_val _ cs off e); [cbn [In]; tauto | byte_tac | ]
end
| match cs with
| context [mkChunk ?co (CZero ?len)] => eapply (cbz_zero _ cs off co len); [cbn [In]; tauto | lia | ]
end ]
end.
Ltac chunk_bytesZ_tac n byte_tac :=
lazymatch n with
| O => apply cbz_nil
| Datatypes.S ?m => chunk_bytesZ_step byte_tac; chunk_bytesZ_tac m byte_tac
end.
Ltac rbyte_hyp n H36 H37 H39 := lazymatch n with 36%nat => H36 | 37%nat => H37 | 39%nat => H39 end.
Ltac rbyte_tac H36 H37 H39 HWr HHr HLr :=
idtac;
lazymatch goal with
| |- (bv_unsigned (sv_denot _ (SLit ?v)) mod 256 = _)%Z => let b := eval vm_compute in (bv_unsigned (Z_to_bv 64 v) mod 256)%Z in exact (eq_refl b)
| |- (bv_unsigned (sv_denot _ (SExt true 16 (SOff ?n 0))) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_sext16 _ _ _ h r)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SExt true 16 (SOff ?n 0)) (SLit 8))) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_sext16_hi _ _ _ h r)
| |- (bv_unsigned (sv_denot _ (SExt false 16 (SOff ?n 0))) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_zext16 _ _ _ h r)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SExt false 16 (SOff ?n 0)) (SLit 8))) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_zext16_hi _ _ _ h r)
| |- (bv_unsigned (sv_denot _ (SOff ?n 0)) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_atom16 _ _ _ h r)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SOff ?n 0) (SLit 8))) mod 256 = _)%Z =>
let h := rbyte_hyp n H36 H37 H39 in let r := rbyte_hyp n HWr HHr HLr in exact (byte_atom16_hi _ _ _ h r)
end.
Ltac add_regionZ HS r :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_region segs E1 ss1 ms1 r) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity | | ]
end.
Ltac stretch_cut HS regs2 mem2 newpc b mlo lo HS2 :=
lazymatch type of HS with st_ok ?segs ?Ec ?ssc ?msc =>
lazymatch Ec with havoc _ ?k0 ?l0 =>
let k := eval vm_compute in (k0 + length l0)%nat in
let rs := eval vm_compute in (memset_cut b mlo lo (ss_mem ssc)) in
pose proof (st_ok_after_stretch segs k Ec ssc msc regs2 mem2 rs newpc MEMSET_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
(submem_memset_cut b mlo lo (ss_mem ssc))
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rs k MEMSET_CLOB newpc) in
change (ss_after_stretch ssc rs k MEMSET_CLOB newpc) with ss2 in HS2
end end.
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Lemma rdn_of_mbyte : forall (m : word -> option byte) n a,
(forall i, 0 <= i < Z.of_nat n -> exists b, mbyte ubs0segs m (a + i) = Some b) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
exists bs, rdn ubs0segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof using.
intros m n. induction n as [|n IH]; intros a Hp Ha Hnw.
- exists []. split; reflexivity.
- destruct (Hp 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb. unfold mbyte in Hb.
destruct (IH (a + 1)) as (bs & Hbs & Hlen); [intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hp; lia | lia | lia |].
exists (b :: bs). split; [|cbn; lia]. cbn [rdn]. rewrite Hb.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [rewrite Hbs; reflexivity|].
apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned 1) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma jmemcpy_rd : forall pcm, memcpy_spec ubs0_msyms pcm ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw,
st_ok ubs0segs E ss ms -> ss_pc ss = pcm -> ss_resv ss = None ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 src -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
0 <= n -> 0 <= d -> 0 <= src -> d + n < 2 ^ 64 -> src + n < 2 ^ 64 ->
(forall i, 0 <= i < n -> present (ms_mem ms) (d + i)) ->
(forall i, 0 <= i < n -> exists b, mbyte ubs0segs (ms_mem ms) (src + i) = Some b) ->
(d + n <= src \/ src + n <= d) ->
(forall a, d <= a < d + n -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) ->
SR ubs0segs (mkCfg ms mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
getr regs2 10 = Z_to_bv 64 d /\
(forall r, reg_in r MEMCPY_CLOB = false -> getr regs2 r = getr (ms_regs ms) r) /\
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> mem2 x = ms_mem ms x) /\
mem_grows (ms_mem ms) mem2 /\
(forall i, 0 <= i < n -> mbyte ubs0segs mem2 (d + i) = mbyte ubs0segs (ms_mem ms) (src + i))).
Proof using IMG LAWS.
intros pcm HM E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw HS Hpc Hrv HJ H10 H11 H12 H1 Hraw
Hn Hd Hs Hdn Hsn Hpd Hps Hdisj HW.
destruct (rdn_of_mbyte (ms_mem ms) (Z.to_nat n) src ltac:(intros i Hi; apply Hps; lia) Hs ltac:(lia)) as (bs & Hbs & Hlen).
pose proof (store_ok_of_present ubs0_msyms (ms_mem ms) (Z.to_nat n) d ltac:(intros i Hi; apply Hpd; lia) Hd ltac:(lia)) as Hst.
rewrite <- Hlen in Hst.
destruct (HM bs (Z_to_bv 64 d) (Z_to_bv 64 src) (Z_to_bv 64 n) (ms_mem ms) (seg_rom ubs0segs) (ms_regs ms) H10 H11 H12)
as (regs2 & Hms & Ha0 & Hfr).
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite Hlen. exact Hbs. }
{ exact Hst. }
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite !unsigned_lit_small by lia. lia. }
rewrite (st_ok_mkst ubs0segs E ss ms HS Hrv), Hpc.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
apply SR_ret. exists regs2, (wbytes (ms_mem ms) (Z_to_bv 64 d) bs). rewrite H1, Hraw.
assert (Hout : forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> wbytes (ms_mem ms) (Z_to_bv 64 d) bs x = ms_mem ms x).
{ intros x Hx. destruct Hx as [Hx|Hx].
- apply wbytes_below; rewrite unsigned_lit_small by lia; lia.
- apply wbytes_above. rewrite unsigned_lit_small by lia. lia. }
split; [reflexivity|]. split.
{ eapply (journal_exec _ _ LAWS IMG) with (W := fun a => d <= a < d + n); [exact HJ | | apply wbytes_grows | exact HW].
intros x Hx. apply Hout. lia. }
split; [exact Ha0|]. split.
{ intros r Hr. destruct (memcpy_clob_out r Hr) as (?&?&?&?&?&?&?&?&?&?&?). apply Hfr; assumption. }
split; [exact Hout|]. split; [apply wbytes_grows|].
intros i Hi. rewrite (wbytes_mbyte ubs0segs bs (ms_mem ms) d (d + i)) by lia.
replace ((d <=? d + i) && (d + i <? d + Z.of_nat (length bs))) with true.
2:{ symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
apply rdn_mbytes in Hbs. destruct Hbs as [_ Hb].
replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by lia.
rewrite <- (Hb (Z.to_nat i)) by lia.
replace (src + Z.of_nat (Z.to_nat i)) with (src + i) by lia. reflexivity.
Qed.
Definition lits_RawConfig : list (option Z) :=
[Some ubs0_A_cgif_writecb; None; None; None; None; None; None; None].
Lemma lits_RawConfig_ok : forall g pgct rattr W H sgct loops,
forall j z, nth_error lits_RawConfig j = Some (Some z) ->
nth_error [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some z.
Proof using.
intros g pgct rattr W H sgct loops j z Hj. do 8 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
Qed.
Lemma raw_obj_final : forall E mem res g pgct rattr W H sgct loops,
Forall (chunk_ok ubs0segs E mem res)
(mkChunk 40 (CVal 4 (SLit 6)) :: obj_chunks_gen LAY_RawConfig 32 lits_RawConfig) ->
(forall j v, nth_error [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v -> ew E (32 + j) = Z_to_bv 64 v) ->
(forall j v, nth_error [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v ->
0 <= v < 2 ^ (8 * Z.of_N (snd (nth j LAY_RawConfig (0, 8%N))))) ->
obj_at ubs0segs mem res LAY_Raw [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops; R_PENDING].
Proof using.
intros E mem res g pgct rattr W H sgct loops Hcs HX HR.
eapply (obj_at_of_chunks_gen ubs0segs E mem res LAY_Raw _ 32 (lits_RawConfig ++ [Some R_PENDING])).
- eapply incl_Forall; [|exact Hcs]. intros c Hc. cbn in Hc. cbn. tauto.
- reflexivity.
- reflexivity.
- intros j v Hj.
assert (Hcase : (j < 8)%nat \/ j = 8%nat \/ (8 < j)%nat) by lia.
destruct Hcase as [Hlt | [-> | Hgt]].
+ assert (Hj8 : nth_error [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v).
{ do 8 (destruct j as [|j]; [exact Hj|]). lia. }
split.
* replace (nth j LAY_Raw (0, 8%N)) with (nth j LAY_RawConfig (0, 8%N)) by (do 8 (destruct j as [|j]; [reflexivity|]); lia).
exact (HR j v Hj8).
* destruct j as [|j]; [cbn in Hj |- *; injection Hj as <-; reflexivity|].
replace (nth_error (lits_RawConfig ++ [Some R_PENDING]) (Datatypes.S j)) with (Some (@None Z)). 2:{ do 7 (destruct j as [|j]; [reflexivity|]). lia. }
hnf. apply (HX (Datatypes.S j) v Hj8).
+ cbn in Hj. injection Hj as <-. cbn. unfold R_PENDING. split; [lia | reflexivity].
+ exfalso. do 9 (destruct j as [|j]; [lia|]). cbn in Hj. destruct j; discriminate Hj.
Qed.
Lemma cgif_obj_of_chunks : forall E mem g gvals {f : Z},
Forall (chunk_ok ubs0segs E mem g) (obj_chunks_gen LAY_CGIF 40 lits_CGIF) ->
length gvals = 17%nat ->
nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
(forall j v, nth_error gvals j = Some v -> ew E (40 + j) = Z_to_bv 64 v) ->
(forall j v, nth_error gvals j = Some v -> 0 <= v < 2 ^ (8 * Z.of_N (snd (nth j LAY_CGIF (0, 8%N))))) ->
obj_at ubs0segs mem g LAY_CGIF gvals.
Proof using.
intros E mem g gvals f Hcs Hlen Hwfn Hfile HY HR.
eapply (obj_at_of_chunks_gen ubs0segs E mem g LAY_CGIF gvals 40 lits_CGIF Hcs eq_refl Hlen).
intros j v Hj. split; [exact (HR j v Hj)|].
pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj. rewrite Hlen in Hlj.
do 17 (try (destruct j as [|j]; [cbn [nth_error lits_CGIF]; first [apply (HY _ _ Hj) | unfold CG_wfn, CG_file in *; congruence] | ])).
lia.
Qed.
Lemma raw_cfg_obj_of_chunks : forall E mem a g pgct rattr W H sgct loops,
Forall (chunk_ok ubs0segs E mem a) (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig) ->
(forall j v, nth_error [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v -> ew E (32 + j) = Z_to_bv 64 v) ->
(forall j v, nth_error [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v ->
0 <= v < 2 ^ (8 * Z.of_N (snd (nth j LAY_RawConfig (0, 8%N))))) ->
obj_at ubs0segs mem a LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops].
Proof using.
intros E mem a g pgct rattr W H sgct loops Hcs HX HR.
eapply (obj_at_of_chunks_gen ubs0segs E mem a LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] 32 lits_RawConfig Hcs eq_refl eq_refl).
intros j v Hj. split; [exact (HR j v Hj)|].
pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj. cbn [length] in Hlj.
destruct j as [|j]; [cbn in Hj |- *; injection Hj as <-; reflexivity|].
replace (nth_error lits_RawConfig (Datatypes.S j)) with (Some (@None Z)) by (do 7 (destruct j as [|j]; [reflexivity|]); lia).
hnf. apply (HX (Datatypes.S j) v Hj).
Qed.
Definition ss_rawnew : sstate :=
mkSS ubs0_A_cgif_raw_newgif sr_atoms
[ YP09.mkRegion (Some 2%nat) (-RAWNEW_DEPTH) 0 (-RAWNEW_DEPTH) 0 [] ;
YP09.mkRegion (Some 10%nat) 0 40 0 0 (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig) ;
YP09.mkRegion (Some 33%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 40 lits_CGIF) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + RAWNEW_STK) (2^63) 4);
(10%nat, mkAF (CEIL_MIN + RAWNEW_STK) (2^63 - 40) 3);
(33%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4);
(38%nat, mkAF 0 65535 0); (35%nat, mkAF 0 (2^32-1) 0); (39%nat, mkAF 0 65535 0) ] [] []).
Lemma rawnew_x_c9 : rn_case API 129 256.
Proof using FWRITE IMG.
intros  L A regs mem md cfgp g pgct rattr W H sgct loops gvals f pga Npg S GCT bq HPRE Hid Ha0 Hcal Hclo Hchi cvals Hcfg Hcrd Hobj Hwfn Hfile Hgin Hfin HSK Hroom Hsp47 Hpal HRq HRM HH Hra Hal16 Hstk0 Hceil H63 Hstw Htp Herr Hac HSTKv HASv HGSv HRSv HDv HFv Hg0 Hg1 Hg16 HFBv HWSv Hf0 Hf1 Hf16 Hsg_r Hat_r Hlp_r E HE HX HY HE2 HE10 HE33 HE38 HE35 HE39 Hspw Hsg L2 A2 regs2 md2 res Hid2 Hres10 Hnz Hres16 b1 b2 Hbl2 Hblc Hwr HRq2 Hfin2 Hq10 HE2' Hbin2 Hb0 Hb1 Hwr' Hgc regs3 Hd10 Hrf Henvblk WR Hranges Hoff Hgf Hgin2 Hgranges Hglen HE36 HE37 HWr HHr HLr HAr regs4 ms2 HJ3 HSKc HS Hk.
Ltac finish_ok HS HJ Hq10 HE Hra Hranges HX :=
lazymatch type of Hq10 with ew _ 61 = Z_to_bv 64 ?res =>
lazymatch type of HE with (forall n r, _ -> ew ?E n = getr ?regs r) =>
let HPR := fresh "HPR" in let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS ltac:(agree_tac) ltac:(vm_compute; reflexivity)) as HPR;
(jreg HS (10%bv:reg) as Hr10); ew_strip_in Hr10; rewrite Hq10 in Hr10;
(jreg HS (1%bv:reg) as Hr1); ew_strip_in Hr1; rewrite (HE 1%nat 1%bv eq_refl) in Hr1;
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
[ exact (proj1 (heap_model _ _ (aa_laws _) _ _ _ _ (proj1 HJ)))
| exact (proj1 (proj2 (heap_model _ _ (aa_laws _) _ _ _ _ (proj1 HJ))))
| lazymatch type of HS with st_ok _ ?Ef ?ssf ?msx =>
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?L2 ?A2 _ ?md2 =>
exists L2, A2, (ms_regs msx), (ms_mem msx), md2, res end;
cbn [ms_regs ms_mem mkst]; rewrite Hr1, Hra; split; [reflexivity|]; split; [exact HJ|]; split; [exact HPR|];
split; [assumption|]; split; [exact Hr10|]; right; split; [assumption|]; split; [assumption|]; split; [do 2 eexists; split; eassumption|];
let Hm := fresh "Hm" in let Hcs := fresh "Hcs" in
pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite Hq10, unsigned_lit_small in Hcs by lia;
apply (raw_obj_final Ef _ res); [exact Hcs | | exact Hranges];
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in let Hlj := fresh "Hlj" in
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; cbn [length] in Hlj;
rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HX j v Hj)
end ]
end end.
Ltac sink_step HSK HFx Hoff Hq10 HE2 Hspw :=
cbn [ms_mem mkst] in HFx;
lazymatch type of HFx with frame_of _ _ _ ?m1 =>
lazymatch type of HSK with sink_at _ ?m0 ?mdx ?fx ?Sx =>
let Hn := fresh "HSKn" in
assert (Hn : sink_at ubs0_msyms m1 mdx fx Sx);
[ apply (sink_at_frame ubs0_msyms m0 m1 mdx fx Sx); [|exact HSK];
let a := fresh "a" in let Ha := fresh "Ha" in let Ha' := fresh "Ha'" in
intros a Ha; pose proof (Hoff a Ha) as Ha';
apply (mbyte_eq_of ubs0_msyms); apply HFx; rewrite unsigned_lit_small by lia;
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [r_base r_wlo r_whi base_val] in Hr; ew_strip_in Hr; rewrite ?Hq10, ?HE2, ?Hspw, ?unsigned_lit_small in Hr by lia; lia |]);
destruct Hin
| clear HSK; rename Hn into HSK ]
end
end.
Ltac sink_now HS HSK Hoff Hq10 HE2 Hspw :=
lazymatch type of HS with st_ok _ _ _ ?msx =>
match goal with HFx : frame_of _ _ _ (ms_mem msx) |- _ => sink_step HSK HFx Hoff Hq10 HE2 Hspw end end.
Ltac cur_fact HS Hbase Hn :=
lazymatch type of HS with st_ok _ ?Ec _ _ =>
lazymatch type of Hbase with ew _ ?n = ?v => assert (Hn : ew Ec n = v) by (ew_strip; exact Hbase) end end.
Ltac raw_byte_tac H36 H37 H39 HWr HHr HLr :=
idtac;
lazymatch goal with
| |- (bv_unsigned (sv_denot _ (SLit ?v)) mod 256 = _)%Z => let b := eval vm_compute in (bv_unsigned (Z_to_bv 64 v) mod 256)%Z in exact (eq_refl b)
| |- (bv_unsigned (sv_denot _ (SExt true 16 (SOff 36 0))) mod 256 = _)%Z => exact (byte_sext16 _ _ _ H36 HWr)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SExt true 16 (SOff 36 0)) (SLit 8))) mod 256 = _)%Z => exact (byte_sext16_hi _ _ _ H36 HWr)
| |- (bv_unsigned (sv_denot _ (SExt true 16 (SOff 37 0))) mod 256 = _)%Z => exact (byte_sext16 _ _ _ H37 HHr)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SExt true 16 (SOff 37 0)) (SLit 8))) mod 256 = _)%Z => exact (byte_sext16_hi _ _ _ H37 HHr)
| |- (bv_unsigned (sv_denot _ (SExt true 16 (SOff 39 0))) mod 256 = _)%Z => exact (byte_sext16 _ _ _ H39 HLr)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SExt true 16 (SOff 39 0)) (SLit 8))) mod 256 = _)%Z => exact (byte_sext16_hi _ _ _ H39 HLr)
end.
Ltac net_fact HS HE35 Hc rattr HNET b :=
let H35 := fresh "HE35c" in cur_fact HS HE35 H35;
rewrite branch_ne_U, U_and_lit, (U_atom _ 35 rattr H35), U_lit in Hc by lia;
assert (HNET : has_net rattr = b) by (rewrite has_net_land; destruct (Z.land rattr 3 =? 1); cbn in Hc; first [reflexivity | discriminate Hc]);
clear Hc H35.
Ltac sink_lists_eq :=
repeat match goal with b := _ : list Z |- _ => subst b end;
unfold hdr13, net19; rewrite ?app_nil_r; repeat rewrite <- app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Ltac sink_eq0 HNET Hs0 :=
idtac; rewrite raw_header_eq, HNET, Hs0; cbn [Z.eqb]; sink_lists_eq.
Ltac sink_eqK k K2 HNET :=
idtac; rewrite (raw_header_class k K2) by first [reflexivity | lia | (cbn; lia)]; rewrite HNET;
try (match goal with |- context [repeat 0 (Z.to_nat ?e)] => replace (Z.to_nat e) with 0%nat by lia; cbn [repeat] end);
(let v := eval vm_compute in (128 + (Z.max 1 k - 1)) in change (128 + (Z.max 1 k - 1)) with v);
sink_lists_eq.
Ltac finish_okS HS HJ Hq10 HE Hra Hranges HX HSKc EQ HRQ :=
lazymatch type of Hq10 with ew _ 61 = Z_to_bv 64 ?res =>
lazymatch type of HE with (forall n r, _ -> ew ?E n = getr ?regs r) =>
let HPR := fresh "HPR" in let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS ltac:(agree_tac) ltac:(vm_compute; reflexivity)) as HPR;
(jreg HS (10%bv:reg) as Hr10); ew_strip_in Hr10; rewrite Hq10 in Hr10;
(jreg HS (1%bv:reg) as Hr1); ew_strip_in Hr1; rewrite (HE 1%nat 1%bv eq_refl) in Hr1;
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
[ exact (proj1 (heap_model _ _ (aa_laws _) _ _ _ _ (proj1 HJ)))
| exact (proj1 (proj2 (heap_model _ _ (aa_laws _) _ _ _ _ (proj1 HJ))))
| lazymatch type of HS with st_ok _ ?Ef ?ssf ?msx =>
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?L2 ?A2 _ ?md2 =>
exists L2, A2, (ms_regs msx), (ms_mem msx), md2, res end;
cbn [ms_regs ms_mem mkst]; rewrite Hr1, Hra; split; [reflexivity|]; split; [exact HJ|]; split; [exact HPR|];
split; [assumption|]; split; [exact Hr10|]; right; split; [assumption|]; split; [assumption|];
split; [ lazymatch type of HSKc with sink_at _ _ _ _ ?Sx => lazymatch goal with |- sink_at _ _ _ _ ?Sg => replace Sg with Sx; [exact HSKc | EQ] end end |];
split; [do 2 eexists; split; eassumption|];
split; [|exact HRQ];
let Hm := fresh "Hm" in let Hcs := fresh "Hcs" in
pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite Hq10, unsigned_lit_small in Hcs by lia;
apply (raw_obj_final Ef _ res); [exact Hcs | | exact Hranges];
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in let Hlj := fresh "Hlj" in
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; cbn [length] in Hlj;
rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HX j v Hj)
end ]
end end.
Ltac class_fact HS K lo HE38 :=
add_fact HS 38%nat (mkAF lo K 0); [| ew_strip; rewrite HE38, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
jbranch ubs0tbl HS.
1:{ exfalso. cur_fact HS HE38 HE38c. rewrite branch_eq_U, (U_atom _ 38 sgct HE38c), U_lit in Hc by lia.
destruct (Z.eqb_spec sgct 0); [lia | discriminate Hc]. }
clear Hc.
class_fact HS 256 129 HE38.
jrun_to LAWS ubs0tbl_ok HS HJ3 ubs0_A_cgif_writecb. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (10%bv:reg) as Ha10_h9. jreg HS (11%bv:reg) as Ha11_h9. jreg HS (12%bv:reg) as Ha12_h9.
jreg HS (2%bv:reg) as Ha2_h9. jreg HS (4%bv:reg) as Ha4_h9. jreg HS (1%bv:reg) as Ha1_h9.
rewrite HE33 in Ha10_h9. rewrite HE2, Hspw in Ha11_h9, Ha2_h9. rewrite (HE 4%nat 4%bv eq_refl), Htp in Ha4_h9.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp_h9 : spZ (ms_regs msx) = spZ regs - 112) by (unfold spZ at 1; rewrite Ha2_h9; apply unsigned_lit_small; lia) end.
pose proof HJ3 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw_h9) & _).
cur_fact HS HE36 HE36c_h9. cur_fact HS HE37 HE37c_h9. cur_fact HS HE39 HE39c_h9.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let rg := eval vm_compute in (nth 1 (ss_mem ssc) (YP09.mkRegion None 0 0 0 0 [])) in
eassert (HG_h9 : garr8 ubs0segs (ms_mem msc) (spZ regs + -104) _);
[ eapply (garr8_of_chunk_bytesZ ubs0segs Ec (ms_mem msc) rg 2%nat (spZ regs) _ (-104));
[ exact (vst_ok_region_nth ubs0segs Ec ssc msc 1%nat rg HS eq_refl) | reflexivity | ew_strip; rewrite HE2; exact Hspw
| cbn [r_chunks]; chunk_bytesZ_tac 13%nat ltac:(rbyte_tac HE36c_h9 HE37c_h9 HE39c_h9 HWr HHr HLr) ]
| ] end.
lazymatch type of HG_h9 with garr8 _ _ _ ?l => set (bs_h9 := l) in HG_h9 end.
assert (Hbl_h9 : length bs_h9 = 13%nat) by reflexivity.
clear HE36c_h9 HE37c_h9 HE39c_h9.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC_h9 : obj_at ubs0segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HY j v Hj)
| ] end.
eapply SR_bind.
{ lazymatch type of HSKc with sink_at _ _ _ _ ?Sx =>
eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := g) (gvals := gvals) (src := spZ regs + -104) (n := 13) (f := f) (S := Sx) (bs := bs_h9) end;
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Ha1_h9 | apply ret_ok_even; vm_compute; reflexivity
| exact Ha10_h9 | exact Ha11_h9 | exact Ha12_h9 | rewrite Hsp_h9; rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | rewrite Hsp_h9; lia | rewrite Hsp_h9; lia | rewrite Hsp_h9; lia
| exact Ha4_h9 | exact HobjC_h9 | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | exact HG_h9 | rewrite Hbl_h9; reflexivity
| lia | lia | lia | rewrite Hsp_h9; lia | repeat rewrite length_app; lia | lia | ].
intros a Ha; exact Ha. }
cbv beta. intros c' (regs_h9 & mem_h9 & md_h9 & -> & HJ_h9 & HP_h9 & Hr10_h9 & HSK_h9 & Hhi_h9 & Hblk_h9). rewrite Hsp_h9 in Hhi_h9.
clear HJ3 HSKc. rename HJ_h9 into HJ3. rename HSK_h9 into HSKc.
lazymatch type of HS with st_ok _ ?Ec _ _ => lazymatch Ec with havoc _ ?k0 ?l0 =>
let k := eval vm_compute in (k0 + length l0)%nat in
jafter_call_keep HS k regs_h9 mem_h9 HP_h9 [0%nat; 1%nat; 2%nat; 3%nat] HS2 end end.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHw.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; intros a Ha.
+ replace a with (res + (a - res)) by lia. apply (Hblk_h9 res 48 (a - res) Hbin2); [lia|].
replace (res + (a - res)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
+ intros _. apply (present_writable ubs0_msyms). replace a with (res + (a - res)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ _ res 48 (a - res) HHw Hbin2 ltac:(lia))).
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_strip; rewrite HE2; exact Hspw | exact Hhi_h9 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 10); [ew_strip; rewrite HE10; apply unsigned_lit_small; lia | exact Hhi_h9 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise ubs0segs _ _ _ 33 _ _ _ _ _ g); [ew_strip; rewrite HE33; apply unsigned_lit_small; lia | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (g + (a - g)) by lia. apply (Hblk_h9 g CGIF_SIZE (a - g) Hgin2); [lia|].
replace (g + (a - g)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_reg HS (10%bv:reg) 0 Hr10_h9.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem_h9 with (ms_mem msx) in HJ3 end.
jrun_to LAWS ubs0tbl_ok HS HJ3 ubs0_A_cgif_writecb. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (10%bv:reg) as Ha10_p9. jreg HS (11%bv:reg) as Ha11_p9. jreg HS (12%bv:reg) as Ha12_p9.
jreg HS (2%bv:reg) as Ha2_p9. jreg HS (4%bv:reg) as Ha4_p9. jreg HS (1%bv:reg) as Ha1_p9.
rewrite HE33 in Ha10_p9. rewrite HE2, Hspw in Ha2_p9. rewrite (HE 4%nat 4%bv eq_refl), Htp in Ha4_p9.
destruct (Hpal ltac:(lia)) as (Hpin_p9 & Hpeq_p9 & Hpsz_p9 & Hpne_p9 & HGCT_p9 & HGlen_p9).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md pga Npg HH Hpin_p9 ltac:(lia)) as (Hp0_p9 & Hp1_p9 & _).
assert (Hpg_p9 : pgct = pga).
{ pose proof (Hranges 2%nat pgct eq_refl) as Hrg2_p9. cbn [nth snd LAY_RawConfig] in Hrg2_p9. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Hrg2_p9.
apply (f_equal bv_unsigned) in Hpeq_p9. rewrite !unsigned_lit_small in Hpeq_p9 by lia. lia. }
pose proof (HX 2%nat pgct eq_refl) as HE34_p9. change (32 + 2)%nat with 34%nat in HE34_p9. rewrite HE34_p9, Hpg_p9 in Ha11_p9.
assert (Hmul_p9 : mul_div M_MUL (ew E 38) (Z_to_bv 64 3) = Z_to_bv 64 (3 * sgct)).
{ rewrite HE38. apply bv_eq. rewrite mul_div_unsigned. cbn [zmd_raw]. rewrite !unsigned_lit_small by lia.
rewrite bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia). lia. }
rewrite Hmul_p9 in Ha12_p9.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp_p9 : spZ (ms_regs msx) = spZ regs - 112) by (unfold spZ at 1; rewrite Ha2_p9; apply unsigned_lit_small; lia) end.
assert (Hpin2_p9 : In (pga, Npg) (blocks L2 A2)) by (rewrite Hbl2; rewrite Hblc in Hpin_p9; apply in_app_iff in Hpin_p9 as [Hq'|Hq']; apply in_app_iff; [left; exact Hq' | right; right; exact Hq']).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHp_p9.
assert (Hpf_p9 : pga + Npg <= f \/ f + FILE_BLOCK <= pga).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L A mem md (pga, Npg) (f, FILE_BLOCK) HH Hpin_p9 Hfin Hpne_p9) as Hd. cbn [fst snd] in Hd. lia. }
set (bs_p9 := firstn (Z.to_nat (3 * sgct)) GCT).
assert (Hbl_p9 : length bs_p9 = Z.to_nat (3 * sgct)) by (subst bs_p9; apply firstn_length_le; lia).
lazymatch type of HS with st_ok _ _ _ ?msc =>
assert (HG_p9 : garr8 ubs0segs (ms_mem msc) pga bs_p9);
[ pose proof (garr8_sub ubs0segs mem pga GCT 0 (Z.to_nat (3 * sgct)) HGCT_p9) as HGs; cbn [skipn Z.of_nat] in HGs; rewrite Z.add_0_r in HGs; fold bs_p9 in HGs;
apply (garr8_frame ubs0segs mem (ms_mem msc) pga bs_p9 HGs); rewrite Hbl_p9, Z2Nat.id by lia;
pose proof HJ3 as (_ & _ & _ & Hkeep & _);
intros a Ha; replace a with (pga + (a - pga)) by lia; apply (Hkeep pga Npg (a - pga) Hpin_p9 Hpin2_p9); [lia|];
replace (pga + (a - pga)) with a by lia; intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia
| ] end.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC_p9 : obj_at ubs0segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HY j v Hj)
| ] end.
eapply SR_bind.
{ lazymatch type of HSKc with sink_at _ _ _ _ ?Sx =>
eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := g) (gvals := gvals) (src := pga) (n := 3 * sgct) (f := f) (S := Sx) (bs := bs_p9) end;
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Ha1_p9 | apply ret_ok_even; vm_compute; reflexivity
| exact Ha10_p9 | exact Ha11_p9 | exact Ha12_p9 | rewrite Hsp_p9; rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | rewrite Hsp_p9; lia | rewrite Hsp_p9; lia | rewrite Hsp_p9; lia
| exact Ha4_p9 | exact HobjC_p9 | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | exact HG_p9 | rewrite Hbl_p9, Z2Nat.id by lia; reflexivity
| lia | lia | lia | rewrite Hsp_p9; lia | repeat rewrite length_app; lia | lia | ].
intros a Ha; exact Ha. }
cbv beta. intros c' (regs_p9 & mem_p9 & md_p9 & -> & HJ_p9 & HP_p9 & Hr10_p9 & HSK_p9 & Hhi_p9 & Hblk_p9). rewrite Hsp_p9 in Hhi_p9.
clear HJ3 HSKc. rename HJ_p9 into HJ3. rename HSK_p9 into HSKc.
assert (HblZ_p9 : Z.of_nat (length bs_p9) = 3 * sgct) by (rewrite Hbl_p9, Z2Nat.id by lia; reflexivity).
lazymatch type of HS with st_ok _ ?Ec _ _ => lazymatch Ec with havoc _ ?k0 ?l0 =>
let k := eval vm_compute in (k0 + length l0)%nat in
jafter_call_keep HS k regs_p9 mem_p9 HP_p9 [0%nat; 1%nat; 2%nat; 3%nat] HS2 end end.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHw.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; intros a Ha.
+ replace a with (res + (a - res)) by lia. apply (Hblk_p9 res 48 (a - res) Hbin2); [lia|].
replace (res + (a - res)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
+ intros _. apply (present_writable ubs0_msyms). replace a with (res + (a - res)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ _ res 48 (a - res) HHw Hbin2 ltac:(lia))).
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_strip; rewrite HE2; exact Hspw | exact Hhi_p9 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 10); [ew_strip; rewrite HE10; apply unsigned_lit_small; lia | exact Hhi_p9 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise ubs0segs _ _ _ 33 _ _ _ _ _ g); [ew_strip; rewrite HE33; apply unsigned_lit_small; lia | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (g + (a - g)) by lia. apply (Hblk_p9 g CGIF_SIZE (a - g) Hgin2); [lia|].
replace (g + (a - g)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_reg HS (10%bv:reg) 0 Hr10_p9.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem_p9 with (ms_mem msx) in HJ3 end.
jrun LAWS ubs0tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jbranch ubs0tbl HS.
+ cur_fact HS HE38 HE38c. rewrite branch_ne_U, (pad_ovf_U _ sgct 256 512 (-256) 768 HE38c) in Hc by lia.
rewrite Z.eqb_refl in Hc. discriminate Hc.
+ clear Hc.
jrun LAWS ubs0tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jbranch ubs0tbl HS.
* cur_fact HS HE38 HE38c. rewrite branch_eq_U, (pad_cnt16_U _ sgct 256 216172782113783808 HE38c), U_lit in Hc by lia.
assert (HsK : sgct = 256) by (destruct (Z.eqb_spec (3 * (256 - sgct)) 0); [lia | discriminate]). clear Hc HE38c.
jrun_to LAWS ubs0tbl_ok HS HJ3 PC_NT. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
let TK := fresh "TK" in let T2 := fresh "T2" in let T8 := fresh "T8" in let T9 := fresh "T9" in let T18 := fresh "T18" in
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [3; 4; 24; 25; 26; 27]%bv HS ltac:(agree_tac) ltac:(vm_compute; reflexivity)) as TK;
(jreg HS (2%bv:reg) as T2); ew_strip_in T2; rewrite HE2, Hspw in T2;
(jreg HS (8%bv:reg) as T8); ew_strip_in T8; rewrite Hq10 in T8;
(jreg HS (9%bv:reg) as T9); ew_strip_in T9; rewrite HE10 in T9;
(jreg HS (18%bv:reg) as T18);
(lazymatch type of HS with st_ok _ ?Ef ?ssf ?msx =>
let Hm := fresh "Hm" in let Hcs := fresh "Hcs" in
assert (TOres : obj_at ubs0segs (ms_mem msx) res LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops]);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); apply Forall_inv in Hm;
  unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
  ew_strip_in Hcs; rewrite Hq10, unsigned_lit_small in Hcs by lia;
  apply (raw_cfg_obj_of_chunks Ef _ res g pgct rattr W H sgct loops Hcs); [| exact Hranges];
  let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in let Hlj := fresh "Hlj" in
  intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; cbn [length] in Hlj;
  rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HX j v Hj)
| ];
assert (TOcfg : obj_at ubs0segs (ms_mem msx) cfgp LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops]);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); do 2 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
  unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
  ew_strip_in Hcs; rewrite HE10, unsigned_lit_small in Hcs by lia;
  apply (raw_cfg_obj_of_chunks Ef _ cfgp g pgct rattr W H sgct loops Hcs); [| exact Hranges];
  let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in let Hlj := fresh "Hlj" in
  intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; cbn [length] in Hlj;
  rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HX j v Hj)
| ];
assert (TOg : obj_at ubs0segs (ms_mem msx) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
  unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
  ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
  apply (cgif_obj_of_chunks Ef _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
  let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in let Hlj := fresh "Hlj" in
  intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
  rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HY j v Hj)
| ]
end);
let HNET0 := fresh "HNET0" in assert (HNET0 : has_net 0 = false) by reflexivity;
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc];
lazymatch goal with |- SR _ (mkCfg (mkst ?rx _ ?mx _) ?mdx) _ =>
eapply (rn_tail API IMG FWRITE L A mem md regs rx L2 A2 mx mdx cfgp g pgct rattr W H sgct loops res f gvals S GCT bq b1 b2);
[ exact HJ3 | exact Hid2 | exact Hra | exact Htp | exact Hsp47 | (lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (frame_savedN_of_region ubs0_msyms 9 E1);
[ exact (vst_ok_region_nth ubs0segs E1 ss1 ms1 1%nat _ HS eq_refl)
| ew_strip; rewrite HE2; exact Hspw
| let rr := fresh "rr" in let d := fresh "d" in let Hrd := fresh "Hrd" in
  intros rr d Hrd; cbv [SAVEDN SAVED firstn In] in Hrd;
  repeat (destruct Hrd as [Hrd | Hrd];
    [ injection Hrd as <- <-; eexists; split; [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_strip; apply HE; reflexivity] | ]);
  destruct Hrd ]
end)
| rewrite T2; f_equal; lia
| apply TK; cbv; tauto | apply TK; cbv; tauto | apply TK; cbv; tauto | apply TK; cbv; tauto | apply TK; cbv; tauto | apply TK; cbv; tauto
| exact T8 | exact T9 | first [exact T18 | rewrite T18; reflexivity]
| exact Hcal | exact Hclo | exact Hchi | exact TOcfg | exact TOres | exact TOg | exact Hwfn | exact Hfile | exact Hgin | exact Hfin
| exact Hbl2 | exact Hblc
| let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply Hwr'; [exact Hbin2 | rewrite HRSv in Hi; exact Hi]
| lazymatch type of HSKc with sink_at _ _ _ _ ?Sx => replace (S ++ YO07.raw_header W H sgct GCT 0 0) with Sx; [exact HSKc | sink_eqK 8 256 HNET0] end
| exact Hroom | exact Hsg | exact HRq2 ]
end.
* cur_fact HS HE38 HE38c. rewrite branch_eq_U, (pad_cnt16_U _ sgct 256 216172782113783808 HE38c), U_lit in Hc by lia.
assert (HsK : sgct <> 256) by (destruct (Z.eqb_spec (3 * (256 - sgct)) 0); [discriminate | lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (2%bv:reg) as W2. ew_strip_in W2. rewrite HE2, Hspw in W2.
jreg HS (4%bv:reg) as W4. ew_strip_in W4. rewrite (HE 4%nat 4%bv eq_refl), Htp in W4.
jreg HS (20%bv:reg) as W20. ew_strip_in W20. rewrite HE33 in W20.
jreg HS (21%bv:reg) as W21. jreg HS (23%bv:reg) as W23.
pose proof (st_ok_reg _ _ _ _ 22%bv HS) as W22. eval_sr_get_in W22.
erewrite (pad_cnt16_denot _ sgct 256 216172782113783808 HE38c) in W22 by lia. clear HE38c.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC_l9 : obj_at ubs0segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HY j v Hj)
| ] end.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HGd_l9 : garr8 ubs0segs (ms_mem msc) (spZ regs - RAWNEW_FRAME + 21) [0]);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
apply Forall_inv_tail in Hm; apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
apply Forall_inv in Hcs; ew_strip_in Hcs; rewrite HE2, Hspw in Hcs;
destruct (Hcs 0 ltac:(cbn; lia)) as (b0 & Hcb & Hmb); cbn [c_off c_val] in Hcb, Hmb; cbn in Hcb; injection Hcb as <-;
intros [|j] Hj; [|cbn in Hj; lia]; cbn [nth Z.of_nat]; split; [|lia];
intros kk Hkk; assert (kk = 0%nat) by lia; subst kk;
match goal with |- mbyte _ _ ?x = _ => replace x with (spZ regs + -91 + 0) by (unfold RAWNEW_FRAME; lia) end;
change (ms_segs ubs0_msyms) with ubs0segs in Hmb; rewrite Hmb; first [reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity]
| ] end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ lazymatch type of HSKc with sink_at _ _ ?mdx _ ?Sx =>
eapply (wdb_loop API IMG FWRITE (Z.to_nat (3 * (256 - sgct))) (3 * (256 - sgct)) _ _ RAWNEW_STK (spZ regs) (sink_fp f) L A _ md L2 A2 mdx g gvals (spZ regs - RAWNEW_FRAME) f Sx) end;
[ lia | lia | exact HJ3 | exact HobjC_l9 | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | repeat rewrite length_app; lia | exact HGd_l9
| intros a Ha; exact Ha
| rewrite W2; f_equal; unfold RAWNEW_FRAME; lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | unfold RAWNEW_FRAME; lia | unfold RAWNEW_FRAME; lia | lia
| exact W4 | exact W20 | exact W23 | exact W21 | exact W22 ]. }
cbv beta. intros c' (regs_l9 & mem_l9 & md_l9 & -> & HJ_l9 & HK_l9 & H23_l9 & H22_l9 & HSK_l9 & Hhi_l9 & Hblk_l9).
clear HJ3 HSKc. rename HJ_l9 into HJ3. rename HSK_l9 into HSKc.
assert (HblZ_l9 : Z.of_nat (length (repeat (0 : Z) (Z.to_nat (3 * (256 - sgct))))) = 3 * (256 - sgct)) by (rewrite repeat_length, Z2Nat.id by lia; reflexivity).
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => lazymatch Ec with havoc _ ?k0 ?l0 =>
let k := eval vm_compute in (k0 + length l0)%nat in
let rs := eval vm_compute in (ss_mem ssc) in
pose proof (st_ok_after_stretch ubs0segs k Ec ssc msc regs_l9 mem_l9 rs WDB_EXIT WDB_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_refl)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HK_l9) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rs k WDB_CLOB WDB_EXIT) in
change (ss_after_stretch ssc rs k WDB_CLOB WDB_EXIT) with ss2 in HS2
end end.
match type of HS2 with ?P -> _ => assert (HKm : P); [| specialize (HS2 HKm); clear HKm] end.
{ unfold RAWNEW_FRAME in Hhi_l9.
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHw.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; intros a Ha.
+ replace a with (res + (a - res)) by lia. apply (Hblk_l9 res 48 (a - res) Hbin2); [lia|].
replace (res + (a - res)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
+ intros _. apply (present_writable ubs0_msyms). replace a with (res + (a - res)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ _ res 48 (a - res) HHw Hbin2 ltac:(lia))).
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_strip; rewrite HE2; exact Hspw | exact Hhi_l9 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 10); [ew_strip; rewrite HE10; apply unsigned_lit_small; lia | exact Hhi_l9 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise ubs0segs _ _ _ 33 _ _ _ _ _ g); [ew_strip; rewrite HE33; apply unsigned_lit_small; lia | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (g + (a - g)) by lia. apply (Hblk_l9 g CGIF_SIZE (a - g) Hgin2); [lia|].
replace (g + (a - g)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_reg HS (23%bv:reg) 0 H23_l9. pin_reg HS (22%bv:reg) 0 H22_l9.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem_l9 with (ms_mem msx) in HJ3 end.
jrun_to LAWS ubs0tbl_ok HS HJ3 PC_NT. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
let TK := fresh "TK" in let T2 := fresh "T2" in let T8 := fresh "T8" in let T9 := fresh "T9" in let T18 := fresh "T18" in
pose proof (regs_kept_of_st_ok _ _ _ _ regs _ [3; 4; 24; 25; 26; 27]%bv HS ltac:(agree_tac) ltac:(vm_compute; reflexivity)) as TK;
(jreg HS (2%bv:reg) as T2); ew_strip_in T2; rewrite HE2, Hspw in T2;
(jreg HS (8%bv:reg) as T8); ew_strip_in T8; rewrite Hq10 in T8;
(jreg HS (9%bv:reg) as T9); ew_strip_in T9; rewrite HE10 in T9;
(jreg HS (18%bv:reg) as T18);
(lazymatch type of HS with st_ok _ ?Ef ?ssf ?msx =>
let Hm := fresh "Hm" in let Hcs := fresh "Hcs" in
assert (TOres : obj_at ubs0segs (ms_mem msx) res LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops]);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); apply Forall_inv in Hm;
  unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
  ew_strip_in Hcs; rewrite Hq10, unsigned_lit_small in Hcs by lia;
  apply (raw_cfg_obj_of_chunks Ef _ res g pgct rattr W H sgct loops Hcs); [| exact Hranges];
  let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in let Hlj := fresh "Hlj" in
  intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; cbn [length] in Hlj;
  rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HX j v Hj)
| ];
assert (TOcfg : obj_at ubs0segs (ms_mem msx) cfgp LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops]);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); do 2 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
  unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
  ew_strip_in Hcs; rewrite HE10, unsigned_lit_small in Hcs by lia;
  apply (raw_cfg_obj_of_chunks Ef _ cfgp g pgct rattr W H sgct loops Hcs); [| exact Hranges];
  let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in let Hlj := fresh "Hlj" in
  intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; cbn [length] in Hlj;
  rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HX j v Hj)
| ];
assert (TOg : obj_at ubs0segs (ms_mem msx) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
  unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
  ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
  apply (cgif_obj_of_chunks Ef _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
  let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in let Hlj := fresh "Hlj" in
  intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
  rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HY j v Hj)
| ]
end);
let HNET0 := fresh "HNET0" in assert (HNET0 : has_net 0 = false) by reflexivity;
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc];
lazymatch goal with |- SR _ (mkCfg (mkst ?rx _ ?mx _) ?mdx) _ =>
eapply (rn_tail API IMG FWRITE L A mem md regs rx L2 A2 mx mdx cfgp g pgct rattr W H sgct loops res f gvals S GCT bq b1 b2);
[ exact HJ3 | exact Hid2 | exact Hra | exact Htp | exact Hsp47 | (lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (frame_savedN_of_region ubs0_msyms 9 E1);
[ exact (vst_ok_region_nth ubs0segs E1 ss1 ms1 1%nat _ HS eq_refl)
| ew_strip; rewrite HE2; exact Hspw
| let rr := fresh "rr" in let d := fresh "d" in let Hrd := fresh "Hrd" in
  intros rr d Hrd; cbv [SAVEDN SAVED firstn In] in Hrd;
  repeat (destruct Hrd as [Hrd | Hrd];
    [ injection Hrd as <- <-; eexists; split; [cbv; tauto | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_strip; apply HE; reflexivity] | ]);
  destruct Hrd ]
end)
| rewrite T2; f_equal; lia
| apply TK; cbv; tauto | apply TK; cbv; tauto | apply TK; cbv; tauto | apply TK; cbv; tauto | apply TK; cbv; tauto | apply TK; cbv; tauto
| exact T8 | exact T9 | first [exact T18 | rewrite T18; reflexivity]
| exact Hcal | exact Hclo | exact Hchi | exact TOcfg | exact TOres | exact TOg | exact Hwfn | exact Hfile | exact Hgin | exact Hfin
| exact Hbl2 | exact Hblc
| let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply Hwr'; [exact Hbin2 | rewrite HRSv in Hi; exact Hi]
| lazymatch type of HSKc with sink_at _ _ _ _ ?Sx => replace (S ++ YO07.raw_header W H sgct GCT 0 0) with Sx; [exact HSKc | sink_eqK 8 256 HNET0] end
| exact Hroom | exact Hsg | exact HRq2 ]
end.
Qed.
End S.
End t.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
