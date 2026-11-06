(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import Utf8.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YI06 YI5b YI09 YI08 YI0r YI1w YN3b YI55.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI5c YI0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI01 YI6c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI02 YI0j.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI4l YI5a YI2v YI5d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_ok_add_region : forall segs E ss ms r,
st_ok segs E ss ms -> region_wf r = true -> region_ok segs E (ms_mem ms) r -> all_disjoint E r (ss_mem ss) ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof. split; reflexivity. Qed.
Lemma LAY_Raw_ok : lay_inside LAY_Raw RAW_SIZE = true /\ lay_widths_ok LAY_Raw = true.
Proof. split; reflexivity. Qed.
Lemma Ereg_vals2 : forall regs vals1 vals2 more j v,
nth_error vals2 j = Some v ->
ew (Ereg regs (map (Z_to_bv 64) vals1 ++ (map (Z_to_bv 64) vals2 ++ more))) (32 + (length vals1 + j)) = Z_to_bv 64 v.
Proof.
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
Proof.
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
Proof.
intros E r rs a. unfold in_wrange. split.
- intros (r' & [<-|Hin] & H); [left; exact H | right; exists r'; auto].
- intros [H | (r' & Hin & H)]; [exists r; split; [left; reflexivity | exact H] | exists r'; split; [right; exact Hin | exact H]].
Qed.
Lemma in_wrange_nil : forall E a, ~ in_wrange E [] a.
Proof. intros E a (r & Hin & _). destruct Hin. Qed.
Lemma wdb_count_val : forall s K, 0 <= s < K -> K <= 256 ->
Z.land (((s * 18446744073709551613) mod 2 ^ 64 + 3 * K) mod 2 ^ 64) 65535 = 3 * (K - s).
Proof.
intros s K Hs HK.
replace (((s * 18446744073709551613) mod 2 ^ 64 + 3 * K) mod 2 ^ 64) with (3 * (K - s)).
2:{ rewrite Zplus_mod_idemp_l. replace (s * 18446744073709551613 + 3 * K) with (3 * (K - s) + s * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma wdb_count_denot : forall E s K c,
ew E 38 = Z_to_bv 64 s -> 0 <= s < K -> K <= 256 -> c = 3 * K ->
sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SMd M_MUL (SOff 38 0) (SLit 18446744073709551613)) (SLit c)) (SLit 65535))
= Z_to_bv 64 (3 * (K - s)).
Proof.
intros E s K c H38 Hs HK ->.
rewrite denot_lit_U. f_equal. rewrite U_and_lit by lia. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom _ 38 s H38), !U_lit by lia. unfold zcanon, M64.
apply wdb_count_val; lia.
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
Proof.
intros segs mem a lay. induction lay as [|f lay IH]; intros [|v' vals] H j v Hj; cbn in H; try tauto; [destruct j; discriminate|].
destruct H as [[_ Hr] H]. destruct j as [|j]; cbn in Hj |- *; [injection Hj as <-; exact Hr | exact (IH vals H j v Hj)].
Qed.
End q.
Ltac agree_tac := first [ apply env_agree_refl | apply env_agree_havoc_ge; [cbv; lia | agree_tac] ].
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Hypothesis FWRITE : fwrite_spec src0_msyms MR src0_A_fwrite.
Lemma rdn_of_mbyte : forall (m : word -> option byte) n a,
(forall i, 0 <= i < Z.of_nat n -> exists b, mbyte src0segs m (a + i) = Some b) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
exists bs, rdn src0segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
intros m n. induction n as [|n IH]; intros a Hp Ha Hnw.
- exists []. split; reflexivity.
- destruct (Hp 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb. unfold mbyte in Hb.
destruct (IH (a + 1)) as (bs & Hbs & Hlen); [intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hp; lia | lia | lia |].
exists (b :: bs). split; [|cbn; lia]. cbn [rdn]. rewrite Hb.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [rewrite Hbs; reflexivity|].
apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned 1) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma jmemcpy_rd : forall pcm, memcpy_spec src0_msyms pcm ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw,
st_ok src0segs E ss ms -> ss_pc ss = pcm -> ss_resv ss = None ->
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 src -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
0 <= n -> 0 <= d -> 0 <= src -> d + n < 2 ^ 64 -> src + n < 2 ^ 64 ->
(forall i, 0 <= i < n -> present (ms_mem ms) (d + i)) ->
(forall i, 0 <= i < n -> exists b, mbyte src0segs (ms_mem ms) (src + i) = Some b) ->
(d + n <= src \/ src + n <= d) ->
(forall a, d <= a < d + n -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) ->
SR src0segs (mkCfg ms mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom src0segs)) mdc /\
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
getr regs2 10 = Z_to_bv 64 d /\
(forall r, reg_in r MEMCPY_CLOB = false -> getr regs2 r = getr (ms_regs ms) r) /\
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> mem2 x = ms_mem ms x) /\
mem_grows (ms_mem ms) mem2 /\
(forall i, 0 <= i < n -> mbyte src0segs mem2 (d + i) = mbyte src0segs (ms_mem ms) (src + i))).
Proof.
intros pcm HM E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw HS Hpc Hrv HJ H10 H11 H12 H1 Hraw
Hn Hd Hs Hdn Hsn Hpd Hps Hdisj HW.
destruct (rdn_of_mbyte (ms_mem ms) (Z.to_nat n) src ltac:(intros i Hi; apply Hps; lia) Hs ltac:(lia)) as (bs & Hbs & Hlen).
pose proof (store_ok_of_present src0_msyms (ms_mem ms) (Z.to_nat n) d ltac:(intros i Hi; apply Hpd; lia) Hd ltac:(lia)) as Hst.
rewrite <- Hlen in Hst.
destruct (HM bs (Z_to_bv 64 d) (Z_to_bv 64 src) (Z_to_bv 64 n) (ms_mem ms) (seg_rom src0segs) (ms_regs ms) H10 H11 H12)
as (regs2 & Hms & Ha0 & Hfr).
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite Hlen. exact Hbs. }
{ exact Hst. }
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite !unsigned_lit_small by lia. lia. }
rewrite (st_ok_mkst src0segs E ss ms HS Hrv), Hpc.
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
intros i Hi. rewrite (wbytes_mbyte src0segs bs (ms_mem ms) d (d + i)) by lia.
replace ((d <=? d + i) && (d + i <? d + Z.of_nat (length bs))) with true.
2:{ symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
apply rdn_mbytes in Hbs. destruct Hbs as [_ Hb].
replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by lia.
rewrite <- (Hb (Z.to_nat i)) by lia.
replace (src + Z.of_nat (Z.to_nat i)) with (src + i) by lia. reflexivity.
Qed.
Definition lits_RawConfig : list (option Z) :=
[Some src0_A_cgif_writecb; None; None; None; None; None; None; None].
Lemma lits_RawConfig_ok : forall g pgct rattr W H sgct loops,
forall j z, nth_error lits_RawConfig j = Some (Some z) ->
nth_error [src0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some z.
Proof.
intros g pgct rattr W H sgct loops j z Hj. do 8 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
Qed.
Lemma raw_obj_final : forall E mem res g pgct rattr W H sgct loops,
Forall (chunk_ok src0segs E mem res)
(mkChunk 40 (CVal 4 (SLit 6)) :: obj_chunks_gen LAY_RawConfig 32 lits_RawConfig) ->
(forall j v, nth_error [src0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v -> ew E (32 + j) = Z_to_bv 64 v) ->
(forall j v, nth_error [src0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v ->
0 <= v < 2 ^ (8 * Z.of_N (snd (nth j LAY_RawConfig (0, 8%N))))) ->
obj_at src0segs mem res LAY_Raw [src0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops; R_PENDING].
Proof.
intros E mem res g pgct rattr W H sgct loops Hcs HX HR.
eapply (obj_at_of_chunks_gen src0segs E mem res LAY_Raw _ 32 (lits_RawConfig ++ [Some R_PENDING])).
- eapply incl_Forall; [|exact Hcs]. intros c Hc. cbn in Hc. cbn. tauto.
- reflexivity.
- reflexivity.
- intros j v Hj.
assert (Hcase : (j < 8)%nat \/ j = 8%nat \/ (8 < j)%nat) by lia.
destruct Hcase as [Hlt | [-> | Hgt]].
+ assert (Hj8 : nth_error [src0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v).
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
Forall (chunk_ok src0segs E mem g) (obj_chunks_gen LAY_CGIF 40 lits_CGIF) ->
length gvals = 17%nat ->
nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
(forall j v, nth_error gvals j = Some v -> ew E (40 + j) = Z_to_bv 64 v) ->
(forall j v, nth_error gvals j = Some v -> 0 <= v < 2 ^ (8 * Z.of_N (snd (nth j LAY_CGIF (0, 8%N))))) ->
obj_at src0segs mem g LAY_CGIF gvals.
Proof.
intros E mem g gvals f Hcs Hlen Hwfn Hfile HY HR.
eapply (obj_at_of_chunks_gen src0segs E mem g LAY_CGIF gvals 40 lits_CGIF Hcs eq_refl Hlen).
intros j v Hj. split; [exact (HR j v Hj)|].
pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj. rewrite Hlen in Hlj.
do 17 (try (destruct j as [|j]; [cbn [nth_error lits_CGIF]; first [apply (HY _ _ Hj) | unfold CG_wfn, CG_file in *; congruence] | ])).
lia.
Qed.
Definition ss_rawnew : sstate :=
mkSS src0_A_cgif_raw_newgif sr_atoms
[ YP09.mkRegion (Some 2%nat) (-RAWNEW_DEPTH) 0 (-RAWNEW_DEPTH) 0 [] ;
YP09.mkRegion (Some 10%nat) 0 40 0 0 (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig) ;
YP09.mkRegion (Some 33%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 40 lits_CGIF) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + RAWNEW_STK) (2^63) 4);
(10%nat, mkAF (CEIL_MIN + RAWNEW_STK) (2^63 - 40) 3);
(33%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4);
(38%nat, mkAF 0 65535 0); (35%nat, mkAF 0 (2^32-1) 0); (39%nat, mkAF 0 65535 0) ] [] []).
Lemma rawnew_x_c7 :
forall (L : layout),
forall (A : astate),
forall (regs : bvmap 5 word),
forall (mem : word → option byte),
forall (md : Model),
forall (cfgp g pgct rattr W H sgct loops : Z),
forall (gvals : list Z),
forall (f pga Npg : Z),
forall (S GCT : list Z),
forall (bq : rbound),
forall (HPRE : fn_pre src0_msyms (aa_MR API) RAWNEW_STK L A regs mem md),
forall (Hid : st_init_done A = true),
forall (Ha0 : getr regs 10 = Z_to_bv 64 cfgp),
forall (Hcal : cfgp mod 8 = 0),
forall (Hclo : spZ regs <= cfgp),
forall (Hchi : cfgp + 40 <= 2 ^ 63),
let cvals : list Z := [src0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] in
forall (Hcfg : obj_at src0segs mem cfgp LAY_RawConfig cvals),
forall (Hcrd : ∀ i : Z, 0 <= i < 40 → ∃ b8 : byte, mbyte src0segs mem (cfgp + i) = Some b8),
forall (Hobj : obj_at src0segs mem g LAY_CGIF gvals),
forall (Hwfn : nth_error gvals CG_wfn = Some 0),
forall (Hfile : nth_error gvals CG_file = Some f),
forall (Hgin : In (g, CGIF_SIZE) (blocks L A)),
forall (Hfin : In (f, FILE_BLOCK) (blocks L A)),
forall (HSK : sink_at src0_msyms mem md f S),
forall (Hroom : Z.of_nat (length S) + 1024 <= SINK_MAX),
forall (Hsp47 : spZ regs <= 2 ^ 47),
forall (Hpal : sgct ≠ 0 → In (pga, Npg) (blocks L A) ∧ Z_to_bv 64 pga = Z_to_bv 64 pgct ∧ 3 * sgct <= Npg ∧ (pga, Npg) ≠ (f, FILE_BLOCK) ∧ garr8 src0segs mem pga GCT ∧ 3 * sgct <= Z.of_nat (length GCT)),
forall (HRq : res_ok A bq),
forall (HRM : rawnew_room bq),
forall (HH : heap_ok (aa_MR API) L A mem md),
forall (Hra : ret_ok (getr regs 1)),
forall (Hal16 : spZ regs mod 16 = 0),
forall (Hstk0 : 0 <= RAWNEW_STK),
forall (Hceil : alloc_ceiling + RAWNEW_STK <= spZ regs),
forall (H63 : spZ regs < 2 ^ 63),
forall (Hstw : ∀ a : Z, spZ regs - RAWNEW_STK <= a < spZ regs → writable_at (ms_segs src0_msyms) mem a),
forall (Htp : getr regs 4 = Z_to_bv 64 (ms_tp src0_msyms)),
forall (Herr : errno_ok src0_msyms mem),
forall (Hac : 140735332483072 <= alloc_ceiling <= 140737479966720),
forall (HSTKv : RAWNEW_STK = 8304),
forall (HASv : ALLOC_STACK = 8192),
forall (HGSv : CGIF_SIZE = 96),
forall (HRSv : RAW_SIZE = 48),
forall (HDv : RAWNEW_DEPTH = 144),
forall (HFv : RAWNEW_FRAME = 112),
forall (Hg0 : 4096 <= g),
forall (Hg1 : g + CGIF_SIZE <= alloc_ceiling),
forall (Hg16 : g mod 16 = 0),
forall (HFBv : FILE_BLOCK = 1264),
forall (HWSv : WRITECB_STK = 528),
forall (Hf0 : 4096 <= f),
forall (Hf1 : f + FILE_BLOCK <= alloc_ceiling),
forall (Hf16 : f mod 16 = 0),
forall (Hsg_r : 0 <= sgct < 2 ^ (8 * Z.of_N 2)),
forall (Hat_r : 0 <= rattr < 2 ^ (8 * Z.of_N 4)),
forall (Hlp_r : 0 <= loops < 2 ^ (8 * Z.of_N 2)),
let E : env := Ereg regs (map (Z_to_bv 64) cvals ++ map (Z_to_bv 64) gvals ++ []) in
forall (HE : ∀ (n : nat) (r : reg), Z.of_nat n = bv_unsigned r → ew E n = getr regs r),
forall (HX : ∀ (j : nat) (v : Z), nth_error cvals j = Some v → ew E (32 + j) = Z_to_bv 64 v),
forall (HY : ∀ (j : nat) (v : Z), nth_error gvals j = Some v → ew E (40 + j) = Z_to_bv 64 v),
forall (HE2 : ew E 2 = getr regs 2),
forall (HE10 : ew E 10 = Z_to_bv 64 cfgp),
forall (HE33 : ew E 33 = Z_to_bv 64 g),
forall (HE38 : ew E 38 = Z_to_bv 64 sgct),
forall (HE35 : ew E 35 = Z_to_bv 64 rattr),
forall (HE39 : ew E 39 = Z_to_bv 64 loops),
forall (Hspw : bv_unsigned (getr regs 2) = spZ regs),
forall (ms : machine_state),
forall (HF : frame_of E
[{| r_base := Some 2%nat; r_lo := -144; r_hi := 0; r_wlo := -144; r_whi := 0; r_chunks := [] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SLit 79056) |}; {| c_off := 8; c_val := CVal 8 (SOff 33 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 34 0) |}; {| c_off := 24; c_val := CVal 4 (SOff 35 0) |};
{| c_off := 28; c_val := CVal 2 (SOff 36 0) |}; {| c_off := 30; c_val := CVal 2 (SOff 37 0) |}; {| c_off := 32; c_val := CVal 2 (SOff 38 0) |}; {| c_off := 34; c_val := CVal 2 (SOff 39 0) |}]
|};
{|
r_base := Some 33%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SOff 40 0) |}; {| c_off := 8; c_val := CVal 8 (SOff 41 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 42 0) |}; {| c_off := 24; c_val := CVal 8 (SOff 43 0) |}; {| c_off := 32; c_val := CVal 8 (SOff 44 0) |};
{| c_off := 40; c_val := CVal 4 (SOff 45 0) |}; {| c_off := 44; c_val := CVal 4 (SOff 46 0) |}; {| c_off := 48; c_val := CVal 2 (SOff 47 0) |}; {| c_off := 50; c_val := CVal 2 (SOff 48 0) |};
{| c_off := 52; c_val := CVal 2 (SOff 49 0) |}; {| c_off := 54; c_val := CVal 2 (SOff 50 0) |}; {| c_off := 56; c_val := CVal 8 (SLit 0) |}; {| c_off := 64; c_val := CVal 8 (SOff 52 0) |}; {| c_off := 72; c_val := CVal 8 (SOff 53 0) |};
{| c_off := 80; c_val := CVal 8 (SOff 54 0) |}; {| c_off := 88; c_val := CVal 4 (SOff 55 0) |}; {| c_off := 92; c_val := CVal 4 (SOff 56 0) |}]
|}]
mem (ms_mem ms)),
forall (HG : mem_grows (ms_mem (mkst regs (Z_to_bv 64 src0_A_cgif_raw_newgif) mem (seg_rom src0segs))) (ms_mem ms)),
forall (Hsg : sgct <= 256),
forall (ms0 : machine_state),
forall (HF0 : frame_of E
[{|
r_base := Some 2%nat;
r_lo := -144;
r_hi := 0;
r_wlo := -144;
r_whi := 0;
r_chunks :=
[{| c_off := -72; c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; c_val := CVal 8 (SOff 1 0) |}]
|};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SLit 79056) |}; {| c_off := 8; c_val := CVal 8 (SOff 33 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 34 0) |}; {| c_off := 24; c_val := CVal 4 (SOff 35 0) |};
{| c_off := 28; c_val := CVal 2 (SOff 36 0) |}; {| c_off := 30; c_val := CVal 2 (SOff 37 0) |}; {| c_off := 32; c_val := CVal 2 (SOff 38 0) |}; {| c_off := 34; c_val := CVal 2 (SOff 39 0) |}]
|};
{|
r_base := Some 33%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SOff 40 0) |}; {| c_off := 8; c_val := CVal 8 (SOff 41 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 42 0) |}; {| c_off := 24; c_val := CVal 8 (SOff 43 0) |}; {| c_off := 32; c_val := CVal 8 (SOff 44 0) |};
{| c_off := 40; c_val := CVal 4 (SOff 45 0) |}; {| c_off := 44; c_val := CVal 4 (SOff 46 0) |}; {| c_off := 48; c_val := CVal 2 (SOff 47 0) |}; {| c_off := 50; c_val := CVal 2 (SOff 48 0) |};
{| c_off := 52; c_val := CVal 2 (SOff 49 0) |}; {| c_off := 54; c_val := CVal 2 (SOff 50 0) |}; {| c_off := 56; c_val := CVal 8 (SLit 0) |}; {| c_off := 64; c_val := CVal 8 (SOff 52 0) |}; {| c_off := 72; c_val := CVal 8 (SOff 53 0) |};
{| c_off := 80; c_val := CVal 8 (SOff 54 0) |}; {| c_off := 88; c_val := CVal 4 (SOff 55 0) |}; {| c_off := 92; c_val := CVal 4 (SOff 56 0) |}]
|}]
(ms_mem ms) (ms_mem ms0)),
forall (HG0 : mem_grows (ms_mem ms) (ms_mem ms0)),
forall (Hr10 : getr (ms_regs ms0) 10 = Z_to_bv 64 48),
forall (Hr2 : getr (ms_regs ms0) 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -112)),
forall (Hr4 : getr (ms_regs ms0) 4 = Z_to_bv 64 (ms_tp src0_msyms)),
forall (Hr1 : getr (ms_regs ms0) 1 = Z_to_bv 64 82920),
forall (K1 : ∀ a : Z, 0 <= a < alloc_ceiling → mbyte src0segs (ms_mem ms0) a = mbyte src0segs mem a),
forall (HSK1 : sink_at src0_msyms (ms_mem ms0) md f S),
forall (L2 : layout),
forall (A2 : astate),
forall (regs2 : bvmap 5 word),
forall (mem2 : word → option byte),
forall (md2 : Model),
forall (res : Z),
forall (Hid2 : st_init_done A2 = true),
forall (HP2 : regs_preserved (ms_regs ms0) regs2),
forall (Hres10 : getr regs2 10 = Z_to_bv 64 res),
forall (Hnz : res ≠ 0),
forall (Hres16 : res mod 16 = 0),
forall (b1 b2 : list (Z * Z)),
forall (Hbl2 : blocks L2 A2 = b1 ++ (res, 48) :: b2),
forall (Hblc : blocks L A = b1 ++ b2),
forall (Hwr : ∀ (blc : list (Z * Z)) (i : Z), In (res, 48) blc → 0 <= i < 48 → wr_byte RAWNEW_STK (spZ regs) [] (blocks L A) blc (res + i)),
forall (Hkeep2 : ∀ b' m i : Z, In (b', m) (blocks L A) → 0 <= i < m → mbyte src0segs mem2 (b' + i) = mbyte src0segs (ms_mem ms0) (b' + i)),
forall (Hhi2 : ∀ x : Z, alloc_ceiling <= x < 2 ^ 64 → ¬ spZ regs - RAWNEW_FRAME - ALLOC_STACK <= x < spZ regs - RAWNEW_FRAME → mbyte src0segs mem2 x = mbyte src0segs (ms_mem ms0) x ∧ (writable_at src0segs (ms_mem ms0) x ↔ writable_at src0segs mem2 x)),
forall (HRq2 : res_ok A2 (rb_malloc bq 48)),
forall (HSK2 : sink_at src0_msyms mem2 md2 f S),
forall (Hfin2 : In (f, FILE_BLOCK) (blocks L2 A2)),
forall (Hq10 : ew (havoc E 57 (map (getr regs2) CLOB)) 61 = Z_to_bv 64 res),
forall (HE2' : ew (havoc E 57 (map (getr regs2) CLOB)) 2 = getr regs 2),
forall (Hbin2 : In (res, 48) (blocks L2 A2)),
forall (HH2 : heap_ok MR L2 A2 mem2 md2),
forall (Hb0 : 4096 <= res),
forall (Hb1 : res + 48 <= alloc_ceiling),
forall (Hwr' : ∀ (blc : list (Z * Z)) (i : Z), In (res, 48) blc → 0 <= i < 48 → wr_byte RAWNEW_STK (spZ regs) (sink_fp f) (blocks L A) blc (res + i)),
forall (ms1 : machine_state),
forall (HJ2 : journal src0_msyms MR RAWNEW_STK (spZ regs) (sink_fp f) L A mem md L2 A2 (ms_mem ms1) md2),
forall (HF1 : frame_of (havoc E 57 (map (getr regs2) CLOB))
[{|
r_base := Some 2%nat;
r_lo := -112;
r_hi := 0;
r_wlo := -112;
r_whi := 0;
r_chunks :=
[{| c_off := -72; c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; c_val := CVal 8 (SOff 1 0) |}]
|};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SLit 79056) |}; {| c_off := 8; c_val := CVal 8 (SOff 33 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 34 0) |}; {| c_off := 24; c_val := CVal 4 (SOff 35 0) |};
{| c_off := 28; c_val := CVal 2 (SOff 36 0) |}; {| c_off := 30; c_val := CVal 2 (SOff 37 0) |}; {| c_off := 32; c_val := CVal 2 (SOff 38 0) |}; {| c_off := 34; c_val := CVal 2 (SOff 39 0) |}]
|};
{|
r_base := Some 33%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SOff 40 0) |}; {| c_off := 8; c_val := CVal 8 (SOff 41 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 42 0) |}; {| c_off := 24; c_val := CVal 8 (SOff 43 0) |}; {| c_off := 32; c_val := CVal 8 (SOff 44 0) |};
{| c_off := 40; c_val := CVal 4 (SOff 45 0) |}; {| c_off := 44; c_val := CVal 4 (SOff 46 0) |}; {| c_off := 48; c_val := CVal 2 (SOff 47 0) |}; {| c_off := 50; c_val := CVal 2 (SOff 48 0) |};
{| c_off := 52; c_val := CVal 2 (SOff 49 0) |}; {| c_off := 54; c_val := CVal 2 (SOff 50 0) |}; {| c_off := 56; c_val := CVal 8 (SLit 0) |}; {| c_off := 64; c_val := CVal 8 (SOff 52 0) |}; {| c_off := 72; c_val := CVal 8 (SOff 53 0) |};
{| c_off := 80; c_val := CVal 8 (SOff 54 0) |}; {| c_off := 88; c_val := CVal 4 (SOff 55 0) |}; {| c_off := 92; c_val := CVal 4 (SOff 56 0) |}]
|}]
(ms_mem (mkst regs2 (Z_to_bv 64 82920) mem2 (seg_rom (ms_segs src0_msyms)))) (ms_mem ms1)),
forall (HG1 : mem_grows (ms_mem (mkst regs2 (Z_to_bv 64 82920) mem2 (seg_rom (ms_segs src0_msyms)))) (ms_mem ms1)),
forall (M10 : getr (ms_regs ms1) 10 = Z_to_bv 64 res),
forall (M11 : getr (ms_regs ms1) 11 = Z_to_bv 64 cfgp),
forall (M12 : getr (ms_regs ms1) 12 = Z_to_bv 64 40),
forall (M1 : getr (ms_regs ms1) 1 = Z_to_bv 64 82940),
forall (Hgc : g + CGIF_SIZE <= res ∨ res + 48 <= g),
forall (Hcfg1 : ∀ i : Z, 0 <= i < 40 → mbyte src0segs (ms_mem ms1) (cfgp + i) = mbyte src0segs mem (cfgp + i)),
forall (regs3 : bvmap 5 word),
forall (mem3 : word → option byte),
forall (Hd10 : getr regs3 10 = Z_to_bv 64 res),
forall (Hfr3 : ∀ r : reg, reg_in r MEMCPY_CLOB = false → getr regs3 r = getr (ms_regs ms1) r),
forall (Hout3 : ∀ x : word, bv_unsigned x < res ∨ res + 40 <= bv_unsigned x → mem3 x = ms_mem ms1 x),
forall (Hgr3 : mem_grows (ms_mem ms1) mem3),
forall (Hcp3 : ∀ i : Z, 0 <= i < 40 → mbyte src0segs mem3 (res + i) = mbyte src0segs (ms_mem ms1) (cfgp + i)),
forall (Hrf : res + 48 <= f ∨ f + FILE_BLOCK <= res),
forall (Henvblk : ∀ (L1 : layout) (A1 : astate) (m1 : word → option byte) (md1 : Model) (b n a : Z), heap_ok MR L1 A1 m1 md1 → In (b, n) (blocks L1 A1) → env_addr a → ¬ b <= a < b + n),
forall (Hraw3 : obj_at src0segs mem3 res LAY_RawConfig cvals),
forall (WR : ∀ (E1 : env) (cs0 cs1 : list YP09.chunk) (lo : Z),
ew E1 61 = Z_to_bv 64 res
→ ew E1 2 = getr regs 2
→ - RAWNEW_STK <= lo
→ wr_ok E1
[{| r_base := Some 61%nat; r_lo := 0; r_hi := 48; r_wlo := 0; r_whi := 48; r_chunks := cs0 |}; {| r_base := Some 2%nat; r_lo := lo; r_hi := 0; r_wlo := lo; r_whi := 0; r_chunks := cs1 |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 40; r_wlo := 0; r_whi := 0; r_chunks := obj_chunks_gen LAY_RawConfig 32 lits_RawConfig |};
{| r_base := Some 33%nat; r_lo := 0; r_hi := CGIF_SIZE; r_wlo := 0; r_whi := 0; r_chunks := obj_chunks_gen LAY_CGIF 40 lits_CGIF |}]
RAWNEW_STK (spZ regs) (sink_fp f) (blocks L A) (blocks L2 A2)),
forall (Hranges : ∀ (j : nat) (v : Z), nth_error cvals j = Some v → 0 <= v < 2 ^ (8 * Z.of_N (nth j LAY_RawConfig (0, 8%N)).2)),
forall (Hoff : ∀ a : Z, f <= a < f + FILE_BLOCK ∨ env_addr a → 0 <= a < alloc_ceiling ∧ ¬ res <= a < res + 48),
forall (Hsegb : segs_below src0segs 140735332483072 = true),
forall (Hgf : g + CGIF_SIZE <= f ∨ f + FILE_BLOCK <= g),
forall (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)),
forall (Hgranges : ∀ (j : nat) (v : Z), nth_error gvals j = Some v → 0 <= v < 2 ^ (8 * Z.of_N (nth j LAY_CGIF (0, 8%N)).2)),
forall (Hglen : length gvals = 17%nat),
forall (HE36 : ew E 36 = Z_to_bv 64 W),
forall (HE37 : ew E 37 = Z_to_bv 64 H),
forall (HWr : 0 <= W < 65536),
forall (HHr : 0 <= H < 65536),
forall (HLr : 0 <= loops < 65536),
forall (HAr : 0 <= rattr < 2 ^ 32),
forall (ms2 : machine_state),
forall (HJ3 : journal src0_msyms MR RAWNEW_STK (spZ regs) (sink_fp f) L A mem md L2 A2 (ms_mem ms2) md2),
forall (HF2 : frame_of (havoc (havoc E 57 (map (getr regs2) CLOB)) 73 (map (getr regs3) (10%bv :: MEMCPY_CLOB)))
[{|
r_base := Some 61%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 0;
r_whi := 48;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SLit 79056) |}; {| c_off := 8; c_val := CVal 8 (SOff 33 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 34 0) |}; {| c_off := 24; c_val := CVal 4 (SOff 35 0) |};
{| c_off := 28; c_val := CVal 2 (SOff 36 0) |}; {| c_off := 30; c_val := CVal 2 (SOff 37 0) |}; {| c_off := 32; c_val := CVal 2 (SOff 38 0) |}; {| c_off := 34; c_val := CVal 2 (SOff 39 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -112;
r_hi := 0;
r_wlo := -112;
r_whi := 0;
r_chunks :=
[{| c_off := -72; c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; c_val := CVal 8 (SOff 1 0) |}]
|};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SLit 79056) |}; {| c_off := 8; c_val := CVal 8 (SOff 33 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 34 0) |}; {| c_off := 24; c_val := CVal 4 (SOff 35 0) |};
{| c_off := 28; c_val := CVal 2 (SOff 36 0) |}; {| c_off := 30; c_val := CVal 2 (SOff 37 0) |}; {| c_off := 32; c_val := CVal 2 (SOff 38 0) |}; {| c_off := 34; c_val := CVal 2 (SOff 39 0) |}]
|};
{|
r_base := Some 33%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SOff 40 0) |}; {| c_off := 8; c_val := CVal 8 (SOff 41 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 42 0) |}; {| c_off := 24; c_val := CVal 8 (SOff 43 0) |}; {| c_off := 32; c_val := CVal 8 (SOff 44 0) |};
{| c_off := 40; c_val := CVal 4 (SOff 45 0) |}; {| c_off := 44; c_val := CVal 4 (SOff 46 0) |}; {| c_off := 48; c_val := CVal 2 (SOff 47 0) |}; {| c_off := 50; c_val := CVal 2 (SOff 48 0) |};
{| c_off := 52; c_val := CVal 2 (SOff 49 0) |}; {| c_off := 54; c_val := CVal 2 (SOff 50 0) |}; {| c_off := 56; c_val := CVal 8 (SLit 0) |}; {| c_off := 64; c_val := CVal 8 (SOff 52 0) |}; {| c_off := 72; c_val := CVal 8 (SOff 53 0) |};
{| c_off := 80; c_val := CVal 8 (SOff 54 0) |}; {| c_off := 88; c_val := CVal 4 (SOff 55 0) |}; {| c_off := 92; c_val := CVal 4 (SOff 56 0) |}]
|}]
mem3 (ms_mem ms2)),
forall (HG2 : mem_grows (ms_mem (mkst regs3 (Z_to_bv 64 (src0_A_cgif_raw_newgif + 84)) mem3 (seg_rom (ms_segs src0_msyms)))) (ms_mem ms2)),
forall (HSKc : sink_at src0_msyms (ms_mem ms2) md2 f S),
forall (HS : st_ok (ms_segs src0_msyms) (havoc (havoc E 57 (map (getr regs2) CLOB)) 73 (map (getr regs3) (10%bv :: MEMCPY_CLOB)))
(add_cond
(mkSS 83036
[SLit 0; SLit 82940; SOff 2 (-112); SOff 3 0; SOff 4 0; SExt true 16 (SOff 37 0); SOff 75 0; SOff 76 0; SOff 61 0; SOff 10 0; SOff 38 0; SAlu ALU_SRL (SExt true 16 (SOff 36 0)) (SLit 8); SAlu ALU_SRL (SExt true 16 (SOff 37 0)) (SLit 8);
SLit 70; SLit 56; SLit 57; SLit 97; SExt true 16 (SOff 36 0); SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 84 0; SOff 70 0; SOff 71 0; SOff 72 0]
[{|
r_base := Some 61%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 0;
r_whi := 48;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SLit 79056) |}; {| c_off := 8; c_val := CVal 8 (SOff 33 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 34 0) |}; {| c_off := 24; c_val := CVal 4 (SOff 35 0) |};
{| c_off := 28; c_val := CVal 2 (SOff 36 0) |}; {| c_off := 30; c_val := CVal 2 (SOff 37 0) |}; {| c_off := 32; c_val := CVal 2 (SOff 38 0) |}; {| c_off := 34; c_val := CVal 2 (SOff 39 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -112;
r_hi := 0;
r_wlo := -112;
r_whi := 0;
r_chunks :=
[{| c_off := -97; c_val := CVal 1 (SAlu ALU_SRL (SExt true 16 (SOff 36 0)) (SLit 8)) |}; {| c_off := -98; c_val := CVal 1 (SExt true 16 (SOff 36 0)) |}; {| c_off := -99; c_val := CVal 1 (SLit 97) |};
{| c_off := -100; c_val := CVal 1 (SLit 57) |}; {| c_off := -93; c_val := CVal 1 (SLit 0) |}; {| c_off := -94; c_val := CVal 1 (SLit 0) |}; {| c_off := -95; c_val := CVal 1 (SAlu ALU_SRL (SExt true 16 (SOff 37 0)) (SLit 8)) |};
{| c_off := -96; c_val := CVal 1 (SExt true 16 (SOff 37 0)) |}; {| c_off := -101; c_val := CVal 1 (SLit 56) |}; {| c_off := -102; c_val := CVal 1 (SLit 70) |}; {| c_off := -103; c_val := CVal 1 (SLit 73) |};
{| c_off := -104; c_val := CVal 1 (SLit 71) |}; {| c_off := -92; c_val := CVal 1 (SLit 0) |}; {| c_off := -72; c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; c_val := CVal 8 (SOff 1 0) |}]
|};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SLit 79056) |}; {| c_off := 8; c_val := CVal 8 (SOff 33 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 34 0) |}; {| c_off := 24; c_val := CVal 4 (SOff 35 0) |};
{| c_off := 28; c_val := CVal 2 (SOff 36 0) |}; {| c_off := 30; c_val := CVal 2 (SOff 37 0) |}; {| c_off := 32; c_val := CVal 2 (SOff 38 0) |}; {| c_off := 34; c_val := CVal 2 (SOff 39 0) |}]
|};
{|
r_base := Some 33%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; c_val := CVal 8 (SOff 40 0) |}; {| c_off := 8; c_val := CVal 8 (SOff 41 0) |}; {| c_off := 16; c_val := CVal 8 (SOff 42 0) |}; {| c_off := 24; c_val := CVal 8 (SOff 43 0) |};
{| c_off := 32; c_val := CVal 8 (SOff 44 0) |}; {| c_off := 40; c_val := CVal 4 (SOff 45 0) |}; {| c_off := 44; c_val := CVal 4 (SOff 46 0) |}; {| c_off := 48; c_val := CVal 2 (SOff 47 0) |};
{| c_off := 50; c_val := CVal 2 (SOff 48 0) |}; {| c_off := 52; c_val := CVal 2 (SOff 49 0) |}; {| c_off := 54; c_val := CVal 2 (SOff 50 0) |}; {| c_off := 56; c_val := CVal 8 (SLit 0) |};
{| c_off := 64; c_val := CVal 8 (SOff 52 0) |}; {| c_off := 72; c_val := CVal 8 (SOff 53 0) |}; {| c_off := 80; c_val := CVal 8 (SOff 54 0) |}; {| c_off := 88; c_val := CVal 4 (SOff 55 0) |};
{| c_off := 92; c_val := CVal 4 (SOff 56 0) |}]
|}]
None
{|
f_atoms :=
[(61%nat, {| af_lo := 4096; af_hi := 140737479966672; af_al2 := 4 |}); (2%nat, {| af_lo := 140735332491376; af_hi := 9223372036854775808; af_al2 := 4 |});
(10%nat, {| af_lo := 140735332491376; af_hi := 9223372036854775768; af_al2 := 3 |}); (33%nat, {| af_lo := 4096; af_hi := 140737479966624; af_al2 := 4 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(35%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_GEU; ac_a := SLit 256; ac_b := SOff 38 0 |}];
f_alias := []
|})
{| ac_c := neg_bc BC_EQ; ac_a := SOff 38 0; ac_b := SLit 0 |})
ms2),
forall (Hs1 : 1 <= sgct),
forall (Hk : 33 <= sgct <= 64),
SR (ms_segs src0_msyms) {| cfg_ms := ms2; cfg_model := md2 |}
(λ c' : config,
∃ (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word → option byte) (md' : Model) (res0 : Z),
c' = {| cfg_ms := mkst regs' (getr regs 1) mem' (seg_rom src0segs); cfg_model := md' |}
∧ journal src0_msyms (aa_MR API) RAWNEW_STK (spZ regs) (sink_fp f) L A mem md L' A' mem' md'
∧ regs_preserved regs regs'
∧ st_init_done A' = true
∧ getr regs' 10 = Z_to_bv 64 res0
∧ (res0 = 0 ∧ 256 < sgct ∧ blocks L' A' = blocks L A ∧ sink_at src0_msyms mem' md' f S ∧ res_ok A' bq
∨ res0 ≠ 0
∧ sgct <= 256
∧ sink_at src0_msyms mem' md' f (S ++ YO07.raw_header W H sgct GCT rattr loops)
∧ (∃ b0 b3 : list (Z * Z), blocks L' A' = b0 ++ (res0, RAW_SIZE) :: b3 ∧ blocks L A = b0 ++ b3)
∧ obj_at src0segs mem' res0 LAY_Raw [src0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops; R_PENDING] ∧ res_ok A' (rawnew_rb bq))).
Proof.
intros L A regs mem md cfgp g pgct rattr W H sgct loops gvals f pga Npg S GCT bq HPRE Hid Ha0 Hcal Hclo Hchi cvals Hcfg Hcrd Hobj Hwfn Hfile Hgin Hfin HSK Hroom Hsp47 Hpal HRq HRM HH Hra Hal16 Hstk0 Hceil H63 Hstw Htp Herr Hac HSTKv HASv HGSv HRSv HDv HFv Hg0 Hg1 Hg16 HFBv HWSv Hf0 Hf1 Hf16 Hsg_r Hat_r Hlp_r E HE HX HY HE2 HE10 HE33 HE38 HE35 HE39 Hspw ms HF HG Hsg ms0 HF0 HG0 Hr10 Hr2 Hr4 Hr1 K1 HSK1 L2 A2 regs2 mem2 md2 res Hid2 HP2 Hres10 Hnz Hres16 b1 b2 Hbl2 Hblc Hwr Hkeep2 Hhi2 HRq2 HSK2 Hfin2 Hq10 HE2' Hbin2 HH2 Hb0 Hb1 Hwr' ms1 HJ2 HF1 HG1 M10 M11 M12 M1 Hgc Hcfg1 regs3 mem3 Hd10 Hfr3 Hout3 Hgr3 Hcp3 Hrf Henvblk Hraw3 WR Hranges Hoff Hsegb Hgf Hgin2 Hgranges Hglen HE36 HE37 HWr HHr HLr HAr ms2 HJ3 HF2 HG2 HSKc HS Hs1 Hk.
Ltac finish_ok HS HJ Hq10 HE Hra Hranges HX :=
lazymatch type of Hq10 with ew _ 61 = Z_to_bv 64 ?res =>
lazymatch type of HE with (forall n r, _ -> ew ?E n = getr ?regs r) =>
let HPR := fresh "HPR" in let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS ltac:(agree_tac) ltac:(vm_compute; reflexivity)) as HPR;
(jreg HS (10%bv:reg) as Hr10); ew_strip_in Hr10; rewrite Hq10 in Hr10;
(jreg HS (1%bv:reg) as Hr1); ew_strip_in Hr1; rewrite (HE 1%nat 1%bv eq_refl) in Hr1;
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
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
assert (Hn : sink_at src0_msyms m1 mdx fx Sx);
[ apply (sink_at_frame src0_msyms m0 m1 mdx fx Sx); [|exact HSK];
let a := fresh "a" in let Ha := fresh "Ha" in let Ha' := fresh "Ha'" in
intros a Ha; pose proof (Hoff a Ha) as Ha';
apply (mbyte_eq_of src0_msyms); apply HFx; rewrite unsigned_lit_small by lia;
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
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
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
class_fact HS 64 33 HE38.
jrun_to LAWS src0tbl_ok HS HJ3 src0_A_cgif_writecb. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (10%bv:reg) as Ha10_h7. jreg HS (11%bv:reg) as Ha11_h7. jreg HS (12%bv:reg) as Ha12_h7.
jreg HS (2%bv:reg) as Ha2_h7. jreg HS (4%bv:reg) as Ha4_h7. jreg HS (1%bv:reg) as Ha1_h7.
rewrite HE33 in Ha10_h7. rewrite HE2, Hspw in Ha11_h7, Ha2_h7. rewrite (HE 4%nat 4%bv eq_refl), Htp in Ha4_h7.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp_h7 : spZ (ms_regs msx) = spZ regs - 112) by (unfold spZ at 1; rewrite Ha2_h7; apply unsigned_lit_small; lia) end.
pose proof HJ3 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw_h7) & _).
cur_fact HS HE36 HE36c_h7. cur_fact HS HE37 HE37c_h7. cur_fact HS HE39 HE39c_h7.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let rg := eval vm_compute in (nth 1 (ss_mem ssc) (YP09.mkRegion None 0 0 0 0 [])) in
eassert (HG_h7 : garr8 src0segs (ms_mem msc) (spZ regs + -104) _);
[ eapply (garr8_of_chunk_bytes src0segs Ec (ms_mem msc) rg 2%nat (spZ regs) _ _ (-104));
[ exact (vst_ok_region_nth src0segs Ec ssc msc 1%nat rg HS eq_refl) | reflexivity | ew_strip; rewrite HE2; exact Hspw
| cbn [r_chunks]; chunk_bytes_tac 13%nat ltac:(raw_byte_tac HE36c_h7 HE37c_h7 HE39c_h7 HWr HHr HLr) ]
| ] end.
lazymatch type of HG_h7 with garr8 _ _ _ ?l => set (bs_h7 := l) in HG_h7 end.
assert (Hbl_h7 : length bs_h7 = 13%nat) by reflexivity.
clear HE36c_h7 HE37c_h7 HE39c_h7.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC_h7 : obj_at src0segs (ms_mem msc) g LAY_CGIF gvals);
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
eapply (jwrite src0_msyms MR LAWS src0_A_cgif_writecb (src0_cgif_writecb API IMG FWRITE))
with (g := g) (gvals := gvals) (src := spZ regs + -104) (n := 13) (f := f) (S := Sx) (bs := bs_h7) end;
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Ha1_h7 | apply ret_ok_even; vm_compute; reflexivity
| exact Ha10_h7 | exact Ha11_h7 | exact Ha12_h7 | rewrite Hsp_h7; rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | rewrite Hsp_h7; lia | rewrite Hsp_h7; lia | rewrite Hsp_h7; lia
| exact Ha4_h7 | exact HobjC_h7 | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | exact HG_h7 | rewrite Hbl_h7; reflexivity
| lia | lia | lia | rewrite Hsp_h7; lia | repeat rewrite length_app; lia | lia | ].
intros a Ha; exact Ha. }
cbv beta. intros c' (regs_h7 & mem_h7 & md_h7 & -> & HJ_h7 & HP_h7 & Hr10_h7 & HSK_h7 & Hhi_h7 & Hblk_h7). rewrite Hsp_h7 in Hhi_h7.
clear HJ3 HSKc. rename HJ_h7 into HJ3. rename HSK_h7 into HSKc.
lazymatch type of HS with st_ok _ ?Ec _ _ => lazymatch Ec with havoc _ ?k0 ?l0 =>
let k := eval vm_compute in (k0 + length l0)%nat in
jafter_call_keep HS k regs_h7 mem_h7 HP_h7 [0%nat; 1%nat; 2%nat; 3%nat] HS2 end end.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHw.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; intros a Ha.
+ replace a with (res + (a - res)) by lia. apply (Hblk_h7 res 48 (a - res) Hbin2); [lia|].
replace (res + (a - res)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
+ intros _. apply (present_writable src0_msyms). replace a with (res + (a - res)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ _ res 48 (a - res) HHw Hbin2 ltac:(lia))).
- eapply (region_kept_stack src0segs _ _ _ 2); [ew_strip; rewrite HE2; exact Hspw | exact Hhi_h7 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src0segs _ _ _ 10); [ew_strip; rewrite HE10; apply unsigned_lit_small; lia | exact Hhi_h7 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise src0segs _ _ _ 33 _ _ _ _ _ g); [ew_strip; rewrite HE33; apply unsigned_lit_small; lia | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (g + (a - g)) by lia. apply (Hblk_h7 g CGIF_SIZE (a - g) Hgin2); [lia|].
replace (g + (a - g)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_reg HS (10%bv:reg) 0 Hr10_h7.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem_h7 with (ms_mem msx) in HJ3 end.
jrun_to LAWS src0tbl_ok HS HJ3 src0_A_cgif_writecb. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (10%bv:reg) as Ha10_p7. jreg HS (11%bv:reg) as Ha11_p7. jreg HS (12%bv:reg) as Ha12_p7.
jreg HS (2%bv:reg) as Ha2_p7. jreg HS (4%bv:reg) as Ha4_p7. jreg HS (1%bv:reg) as Ha1_p7.
rewrite HE33 in Ha10_p7. rewrite HE2, Hspw in Ha2_p7. rewrite (HE 4%nat 4%bv eq_refl), Htp in Ha4_p7.
destruct (Hpal ltac:(lia)) as (Hpin_p7 & Hpeq_p7 & Hpsz_p7 & Hpne_p7 & HGCT_p7 & HGlen_p7).
destruct (heap_blocks_range src0_msyms MR LAWS L A mem md pga Npg HH Hpin_p7 ltac:(lia)) as (Hp0_p7 & Hp1_p7 & _).
assert (Hpg_p7 : pgct = pga).
{ pose proof (Hranges 2%nat pgct eq_refl) as Hrg2_p7. cbn [nth snd LAY_RawConfig] in Hrg2_p7. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Hrg2_p7.
apply (f_equal bv_unsigned) in Hpeq_p7. rewrite !unsigned_lit_small in Hpeq_p7 by lia. lia. }
pose proof (HX 2%nat pgct eq_refl) as HE34_p7. change (32 + 2)%nat with 34%nat in HE34_p7. rewrite HE34_p7, Hpg_p7 in Ha11_p7.
assert (Hmul_p7 : mul_div M_MUL (ew E 38) (Z_to_bv 64 3) = Z_to_bv 64 (3 * sgct)).
{ rewrite HE38. apply bv_eq. rewrite mul_div_unsigned. cbn [zmd_raw]. rewrite !unsigned_lit_small by lia.
rewrite bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia). lia. }
rewrite Hmul_p7 in Ha12_p7.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp_p7 : spZ (ms_regs msx) = spZ regs - 112) by (unfold spZ at 1; rewrite Ha2_p7; apply unsigned_lit_small; lia) end.
assert (Hpin2_p7 : In (pga, Npg) (blocks L2 A2)) by (rewrite Hbl2; rewrite Hblc in Hpin_p7; apply in_app_iff in Hpin_p7 as [Hq'|Hq']; apply in_app_iff; [left; exact Hq' | right; right; exact Hq']).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHp_p7.
assert (Hpf_p7 : pga + Npg <= f \/ f + FILE_BLOCK <= pga).
{ pose proof (heap_sep_in2 src0_msyms MR LAWS L A mem md (pga, Npg) (f, FILE_BLOCK) HH Hpin_p7 Hfin Hpne_p7) as Hd. cbn [fst snd] in Hd. lia. }
set (bs_p7 := firstn (Z.to_nat (3 * sgct)) GCT).
assert (Hbl_p7 : length bs_p7 = Z.to_nat (3 * sgct)) by (subst bs_p7; apply firstn_length_le; lia).
lazymatch type of HS with st_ok _ _ _ ?msc =>
assert (HG_p7 : garr8 src0segs (ms_mem msc) pga bs_p7);
[ pose proof (garr8_sub src0segs mem pga GCT 0 (Z.to_nat (3 * sgct)) HGCT_p7) as HGs; cbn [skipn Z.of_nat] in HGs; rewrite Z.add_0_r in HGs; fold bs_p7 in HGs;
apply (garr8_frame src0segs mem (ms_mem msc) pga bs_p7 HGs); rewrite Hbl_p7, Z2Nat.id by lia;
pose proof HJ3 as (_ & _ & _ & Hkeep & _);
intros a Ha; replace a with (pga + (a - pga)) by lia; apply (Hkeep pga Npg (a - pga) Hpin_p7 Hpin2_p7); [lia|];
replace (pga + (a - pga)) with a by lia; intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia
| ] end.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC_p7 : obj_at src0segs (ms_mem msc) g LAY_CGIF gvals);
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
eapply (jwrite src0_msyms MR LAWS src0_A_cgif_writecb (src0_cgif_writecb API IMG FWRITE))
with (g := g) (gvals := gvals) (src := pga) (n := 3 * sgct) (f := f) (S := Sx) (bs := bs_p7) end;
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Ha1_p7 | apply ret_ok_even; vm_compute; reflexivity
| exact Ha10_p7 | exact Ha11_p7 | exact Ha12_p7 | rewrite Hsp_p7; rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | rewrite Hsp_p7; lia | rewrite Hsp_p7; lia | rewrite Hsp_p7; lia
| exact Ha4_p7 | exact HobjC_p7 | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | exact HG_p7 | rewrite Hbl_p7, Z2Nat.id by lia; reflexivity
| lia | lia | lia | rewrite Hsp_p7; lia | repeat rewrite length_app; lia | lia | ].
intros a Ha; exact Ha. }
cbv beta. intros c' (regs_p7 & mem_p7 & md_p7 & -> & HJ_p7 & HP_p7 & Hr10_p7 & HSK_p7 & Hhi_p7 & Hblk_p7). rewrite Hsp_p7 in Hhi_p7.
clear HJ3 HSKc. rename HJ_p7 into HJ3. rename HSK_p7 into HSKc.
assert (HblZ_p7 : Z.of_nat (length bs_p7) = 3 * sgct) by (rewrite Hbl_p7, Z2Nat.id by lia; reflexivity).
lazymatch type of HS with st_ok _ ?Ec _ _ => lazymatch Ec with havoc _ ?k0 ?l0 =>
let k := eval vm_compute in (k0 + length l0)%nat in
jafter_call_keep HS k regs_p7 mem_p7 HP_p7 [0%nat; 1%nat; 2%nat; 3%nat] HS2 end end.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHw.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; intros a Ha.
+ replace a with (res + (a - res)) by lia. apply (Hblk_p7 res 48 (a - res) Hbin2); [lia|].
replace (res + (a - res)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
+ intros _. apply (present_writable src0_msyms). replace a with (res + (a - res)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ _ res 48 (a - res) HHw Hbin2 ltac:(lia))).
- eapply (region_kept_stack src0segs _ _ _ 2); [ew_strip; rewrite HE2; exact Hspw | exact Hhi_p7 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src0segs _ _ _ 10); [ew_strip; rewrite HE10; apply unsigned_lit_small; lia | exact Hhi_p7 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise src0segs _ _ _ 33 _ _ _ _ _ g); [ew_strip; rewrite HE33; apply unsigned_lit_small; lia | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (g + (a - g)) by lia. apply (Hblk_p7 g CGIF_SIZE (a - g) Hgin2); [lia|].
replace (g + (a - g)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_reg HS (10%bv:reg) 0 Hr10_p7.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem_p7 with (ms_mem msx) in HJ3 end.
jrun_to LAWS src0tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jbranch src0tbl HS.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct = 64) by (destruct (Z.eqb_spec 64 sgct); [lia | discriminate]). clear Hc HE38c.
jrun LAWS src0tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jbranch src0tbl HS.
* net_fact HS HE35 Hc rattr HNET false.
jrun LAWS src0tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
finish_okS HS HJ3 Hq10 HE Hra Hranges HX HSKc ltac:(sink_eqK 6 64 HNET) HRq2.
* net_fact HS HE35 Hc rattr HNET true.
jrun_to LAWS src0tbl_ok HS HJ3 src0_A_cgif_writecb. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (10%bv:reg) as Ha10_n7e. jreg HS (11%bv:reg) as Ha11_n7e. jreg HS (12%bv:reg) as Ha12_n7e.
jreg HS (2%bv:reg) as Ha2_n7e. jreg HS (4%bv:reg) as Ha4_n7e. jreg HS (1%bv:reg) as Ha1_n7e.
rewrite HE33 in Ha10_n7e. rewrite HE2, Hspw in Ha11_n7e, Ha2_n7e. rewrite (HE 4%nat 4%bv eq_refl), Htp in Ha4_n7e.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp_n7e : spZ (ms_regs msx) = spZ regs - 112) by (unfold spZ at 1; rewrite Ha2_n7e; apply unsigned_lit_small; lia) end.
pose proof HJ3 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw_n7e) & _).
cur_fact HS HE36 HE36c_n7e. cur_fact HS HE37 HE37c_n7e. cur_fact HS HE39 HE39c_n7e.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let rg := eval vm_compute in (nth 1 (ss_mem ssc) (YP09.mkRegion None 0 0 0 0 [])) in
eassert (HG_n7e : garr8 src0segs (ms_mem msc) (spZ regs + -91) _);
[ eapply (garr8_of_chunk_bytes src0segs Ec (ms_mem msc) rg 2%nat (spZ regs) _ _ (-91));
[ exact (vst_ok_region_nth src0segs Ec ssc msc 1%nat rg HS eq_refl) | reflexivity | ew_strip; rewrite HE2; exact Hspw
| cbn [r_chunks]; chunk_bytes_tac 19%nat ltac:(raw_byte_tac HE36c_n7e HE37c_n7e HE39c_n7e HWr HHr HLr) ]
| ] end.
lazymatch type of HG_n7e with garr8 _ _ _ ?l => set (bs_n7e := l) in HG_n7e end.
assert (Hbl_n7e : length bs_n7e = 19%nat) by reflexivity.
clear HE36c_n7e HE37c_n7e HE39c_n7e.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC_n7e : obj_at src0segs (ms_mem msc) g LAY_CGIF gvals);
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
eapply (jwrite src0_msyms MR LAWS src0_A_cgif_writecb (src0_cgif_writecb API IMG FWRITE))
with (g := g) (gvals := gvals) (src := spZ regs + -91) (n := 19) (f := f) (S := Sx) (bs := bs_n7e) end;
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Ha1_n7e | apply ret_ok_even; vm_compute; reflexivity
| exact Ha10_n7e | exact Ha11_n7e | exact Ha12_n7e | rewrite Hsp_n7e; rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | rewrite Hsp_n7e; lia | rewrite Hsp_n7e; lia | rewrite Hsp_n7e; lia
| exact Ha4_n7e | exact HobjC_n7e | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | exact HG_n7e | rewrite Hbl_n7e; reflexivity
| lia | lia | lia | rewrite Hsp_n7e; lia | repeat rewrite length_app; lia | lia | ].
intros a Ha; exact Ha. }
cbv beta. intros c' (regs_n7e & mem_n7e & md_n7e & -> & HJ_n7e & HP_n7e & Hr10_n7e & HSK_n7e & Hhi_n7e & Hblk_n7e). rewrite Hsp_n7e in Hhi_n7e.
clear HJ3 HSKc. rename HJ_n7e into HJ3. rename HSK_n7e into HSKc.
lazymatch type of HS with st_ok _ ?Ec _ _ => lazymatch Ec with havoc _ ?k0 ?l0 =>
let k := eval vm_compute in (k0 + length l0)%nat in
jafter_call_keep HS k regs_n7e mem_n7e HP_n7e [0%nat; 1%nat; 2%nat; 3%nat] HS2 end end.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHw.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; intros a Ha.
+ replace a with (res + (a - res)) by lia. apply (Hblk_n7e res 48 (a - res) Hbin2); [lia|].
replace (res + (a - res)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
+ intros _. apply (present_writable src0_msyms). replace a with (res + (a - res)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ _ res 48 (a - res) HHw Hbin2 ltac:(lia))).
- eapply (region_kept_stack src0segs _ _ _ 2); [ew_strip; rewrite HE2; exact Hspw | exact Hhi_n7e | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src0segs _ _ _ 10); [ew_strip; rewrite HE10; apply unsigned_lit_small; lia | exact Hhi_n7e | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise src0segs _ _ _ 33 _ _ _ _ _ g); [ew_strip; rewrite HE33; apply unsigned_lit_small; lia | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (g + (a - g)) by lia. apply (Hblk_n7e g CGIF_SIZE (a - g) Hgin2); [lia|].
replace (g + (a - g)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_reg HS (10%bv:reg) 0 Hr10_n7e.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem_n7e with (ms_mem msx) in HJ3 end.
jrun LAWS src0tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
finish_okS HS HJ3 Hq10 HE Hra Hranges HX HSKc ltac:(sink_eqK 6 64 HNET) HRq2.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct <> 64) by (destruct (Z.eqb_spec 64 sgct); [discriminate | lia]). clear Hc HE38c.
jrun_to LAWS src0tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (2%bv:reg) as W2. ew_strip_in W2. rewrite HE2, Hspw in W2.
jreg HS (4%bv:reg) as W4. ew_strip_in W4. rewrite (HE 4%nat 4%bv eq_refl), Htp in W4.
jreg HS (20%bv:reg) as W20. ew_strip_in W20. rewrite HE33 in W20.
jreg HS (21%bv:reg) as W21. jreg HS (22%bv:reg) as W22.
pose proof (st_ok_reg _ _ _ _ 23%bv HS) as W23. eval_sr_get_in W23.
cur_fact HS HE38 HE38c. erewrite (wdb_count_denot _ sgct 64 192 HE38c) in W23 by lia. clear HE38c.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC_l7 : obj_at src0segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HY j v Hj)
| ] end.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HGd_l7 : garr8 src0segs (ms_mem msc) (spZ regs - RAWNEW_FRAME + 21) [0]);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
apply Forall_inv_tail in Hm; apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
apply Forall_inv in Hcs; ew_strip_in Hcs; rewrite HE2, Hspw in Hcs;
destruct (Hcs 0 ltac:(cbn; lia)) as (b0 & Hcb & Hmb); cbn [c_off c_val] in Hcb, Hmb; cbn in Hcb; injection Hcb as <-;
intros [|j] Hj; [|cbn in Hj; lia]; cbn [nth Z.of_nat]; split; [|lia];
intros kk Hkk; assert (kk = 0%nat) by lia; subst kk;
match goal with |- mbyte _ _ ?x = _ => replace x with (spZ regs + -91 + 0) by (unfold RAWNEW_FRAME; lia) end;
change (ms_segs src0_msyms) with src0segs in Hmb; rewrite Hmb; first [reflexivity | f_equal; apply bv_eq; vm_compute; reflexivity]
| ] end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ lazymatch type of HSKc with sink_at _ _ ?mdx _ ?Sx =>
eapply (wdb_loop API IMG FWRITE (Z.to_nat (3 * (64 - sgct))) (3 * (64 - sgct)) _ _ RAWNEW_STK (spZ regs) (sink_fp f) L A _ md L2 A2 mdx g gvals (spZ regs - RAWNEW_FRAME) f Sx) end;
[ lia | lia | exact HJ3 | exact HobjC_l7 | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | repeat rewrite length_app; lia | exact HGd_l7
| intros a Ha; exact Ha
| rewrite W2; f_equal; unfold RAWNEW_FRAME; lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | unfold RAWNEW_FRAME; lia | unfold RAWNEW_FRAME; lia | lia
| exact W4 | exact W20 | exact W21 | exact W22 | exact W23 ]. }
cbv beta. intros c' (regs_l7 & mem_l7 & md_l7 & -> & HJ_l7 & HK_l7 & H21_l7 & H23_l7 & HSK_l7 & Hhi_l7 & Hblk_l7).
clear HJ3 HSKc. rename HJ_l7 into HJ3. rename HSK_l7 into HSKc.
assert (HblZ_l7 : Z.of_nat (length (repeat (0 : Z) (Z.to_nat (3 * (64 - sgct))))) = 3 * (64 - sgct)) by (rewrite repeat_length, Z2Nat.id by lia; reflexivity).
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => lazymatch Ec with havoc _ ?k0 ?l0 =>
let k := eval vm_compute in (k0 + length l0)%nat in
let rs := eval vm_compute in (ss_mem ssc) in
pose proof (st_ok_after_stretch src0segs k Ec ssc msc regs_l7 mem_l7 rs WDB_EXIT WDB_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_refl)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HK_l7) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rs k WDB_CLOB WDB_EXIT) in
change (ss_after_stretch ssc rs k WDB_CLOB WDB_EXIT) with ss2 in HS2
end end.
match type of HS2 with ?P -> _ => assert (HKm : P); [| specialize (HS2 HKm); clear HKm] end.
{ unfold RAWNEW_FRAME in Hhi_l7.
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHw.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; intros a Ha.
+ replace a with (res + (a - res)) by lia. apply (Hblk_l7 res 48 (a - res) Hbin2); [lia|].
replace (res + (a - res)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
+ intros _. apply (present_writable src0_msyms). replace a with (res + (a - res)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ _ res 48 (a - res) HHw Hbin2 ltac:(lia))).
- eapply (region_kept_stack src0segs _ _ _ 2); [ew_strip; rewrite HE2; exact Hspw | exact Hhi_l7 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src0segs _ _ _ 10); [ew_strip; rewrite HE10; apply unsigned_lit_small; lia | exact Hhi_l7 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise src0segs _ _ _ 33 _ _ _ _ _ g); [ew_strip; rewrite HE33; apply unsigned_lit_small; lia | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (g + (a - g)) by lia. apply (Hblk_l7 g CGIF_SIZE (a - g) Hgin2); [lia|].
replace (g + (a - g)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_reg HS (21%bv:reg) 0 H21_l7. pin_reg HS (23%bv:reg) 0 H23_l7.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem_l7 with (ms_mem msx) in HJ3 end.
jrun LAWS src0tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jbranch src0tbl HS.
* net_fact HS HE35 Hc rattr HNET false.
jrun LAWS src0tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
finish_okS HS HJ3 Hq10 HE Hra Hranges HX HSKc ltac:(sink_eqK 6 64 HNET) HRq2.
* net_fact HS HE35 Hc rattr HNET true.
jrun_to LAWS src0tbl_ok HS HJ3 src0_A_cgif_writecb. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (10%bv:reg) as Ha10_n7. jreg HS (11%bv:reg) as Ha11_n7. jreg HS (12%bv:reg) as Ha12_n7.
jreg HS (2%bv:reg) as Ha2_n7. jreg HS (4%bv:reg) as Ha4_n7. jreg HS (1%bv:reg) as Ha1_n7.
rewrite HE33 in Ha10_n7. rewrite HE2, Hspw in Ha11_n7, Ha2_n7. rewrite (HE 4%nat 4%bv eq_refl), Htp in Ha4_n7.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp_n7 : spZ (ms_regs msx) = spZ regs - 112) by (unfold spZ at 1; rewrite Ha2_n7; apply unsigned_lit_small; lia) end.
pose proof HJ3 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw_n7) & _).
cur_fact HS HE36 HE36c_n7. cur_fact HS HE37 HE37c_n7. cur_fact HS HE39 HE39c_n7.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let rg := eval vm_compute in (nth 1 (ss_mem ssc) (YP09.mkRegion None 0 0 0 0 [])) in
eassert (HG_n7 : garr8 src0segs (ms_mem msc) (spZ regs + -91) _);
[ eapply (garr8_of_chunk_bytes src0segs Ec (ms_mem msc) rg 2%nat (spZ regs) _ _ (-91));
[ exact (vst_ok_region_nth src0segs Ec ssc msc 1%nat rg HS eq_refl) | reflexivity | ew_strip; rewrite HE2; exact Hspw
| cbn [r_chunks]; chunk_bytes_tac 19%nat ltac:(raw_byte_tac HE36c_n7 HE37c_n7 HE39c_n7 HWr HHr HLr) ]
| ] end.
lazymatch type of HG_n7 with garr8 _ _ _ ?l => set (bs_n7 := l) in HG_n7 end.
assert (Hbl_n7 : length bs_n7 = 19%nat) by reflexivity.
clear HE36c_n7 HE37c_n7 HE39c_n7.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC_n7 : obj_at src0segs (ms_mem msc) g LAY_CGIF gvals);
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
eapply (jwrite src0_msyms MR LAWS src0_A_cgif_writecb (src0_cgif_writecb API IMG FWRITE))
with (g := g) (gvals := gvals) (src := spZ regs + -91) (n := 19) (f := f) (S := Sx) (bs := bs_n7) end;
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Ha1_n7 | apply ret_ok_even; vm_compute; reflexivity
| exact Ha10_n7 | exact Ha11_n7 | exact Ha12_n7 | rewrite Hsp_n7; rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | rewrite Hsp_n7; lia | rewrite Hsp_n7; lia | rewrite Hsp_n7; lia
| exact Ha4_n7 | exact HobjC_n7 | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | exact HG_n7 | rewrite Hbl_n7; reflexivity
| lia | lia | lia | rewrite Hsp_n7; lia | repeat rewrite length_app; lia | lia | ].
intros a Ha; exact Ha. }
cbv beta. intros c' (regs_n7 & mem_n7 & md_n7 & -> & HJ_n7 & HP_n7 & Hr10_n7 & HSK_n7 & Hhi_n7 & Hblk_n7). rewrite Hsp_n7 in Hhi_n7.
clear HJ3 HSKc. rename HJ_n7 into HJ3. rename HSK_n7 into HSKc.
lazymatch type of HS with st_ok _ ?Ec _ _ => lazymatch Ec with havoc _ ?k0 ?l0 =>
let k := eval vm_compute in (k0 + length l0)%nat in
jafter_call_keep HS k regs_n7 mem_n7 HP_n7 [0%nat; 1%nat; 2%nat; 3%nat] HS2 end end.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HHw.
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; intros a Ha.
+ replace a with (res + (a - res)) by lia. apply (Hblk_n7 res 48 (a - res) Hbin2); [lia|].
replace (res + (a - res)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia.
+ intros _. apply (present_writable src0_msyms). replace a with (res + (a - res)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ _ res 48 (a - res) HHw Hbin2 ltac:(lia))).
- eapply (region_kept_stack src0segs _ _ _ 2); [ew_strip; rewrite HE2; exact Hspw | exact Hhi_n7 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src0segs _ _ _ 10); [ew_strip; rewrite HE10; apply unsigned_lit_small; lia | exact Hhi_n7 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise src0segs _ _ _ 33 _ _ _ _ _ g); [ew_strip; rewrite HE33; apply unsigned_lit_small; lia | | cbn; lia].
intros a Ha. cbn [r_lo r_hi] in Ha. replace a with (g + (a - g)) by lia. apply (Hblk_n7 g CGIF_SIZE (a - g) Hgin2); [lia|].
replace (g + (a - g)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia. }
clear HS. rename HS2 into HS.
pin_reg HS (10%bv:reg) 0 Hr10_n7.
lazymatch type of HS with st_ok _ _ _ ?msx => change mem_n7 with (ms_mem msx) in HJ3 end.
jrun LAWS src0tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
finish_okS HS HJ3 Hq10 HE Hra Hranges HX HSKc ltac:(sink_eqK 6 64 HNET) HRq2.
Qed.
End S.
End t.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
