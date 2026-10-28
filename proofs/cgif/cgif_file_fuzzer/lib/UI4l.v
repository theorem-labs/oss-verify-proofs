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
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0r UI1w UN3b UI55.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 UI5c YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI01 YI6c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI02 YI0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
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
Lemma wdb_count_val : forall s K, 0 <= s < K -> K <= 256 ->
Z.land (((s * 18446744073709551613) mod 2 ^ 64 + 3 * K) mod 2 ^ 64) 65535 = 3 * (K - s).
Proof using.
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
Proof using.
intros E s K c H38 Hs HK ->.
rewrite denot_lit_U. f_equal. rewrite U_and_lit by lia. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom _ 38 s H38), !U_lit by lia. unfold zcanon, M64.
apply wdb_count_val; lia.
Qed.
End p.
Ltac ew_strip :=
repeat match goal with
| |- context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) by (cbv; lia)
end.
Ltac ew_strip_in H :=
repeat match type of H with
| context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) in H by (cbv; lia)
end.
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma obj_at_range : forall segs mem a lay vals,
obj_at segs mem a lay vals -> forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ (8 * Z.of_N (snd (nth j lay (0, 8%N)))).
Proof using.
intros segs mem a lay. induction lay as [|f lay IH]; intros [|v' vals] H j v Hj; cbn in H; try tauto; [destruct j; discriminate|].
destruct H as [[_ Hr] H]. destruct j as [|j]; cbn in Hj |- *; [injection Hj as <-; exact Hr | exact (IH vals H j v Hj)].
Qed.
End t.
Ltac agree_tac := first [ apply env_agree_refl | apply env_agree_havoc_ge; [cbv; lia | agree_tac] ].
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Definition RAWNEW_FRAME : Z := 112.
Definition RAWNEW_DEPTH : Z := 144.
Definition RAWNEW_STK : Z := RAWNEW_FRAME + ALLOC_STACK.
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
rewrite !ew_havoc_old by lia; apply (HX j v Hj)
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
Ltac finish_okS HS HJ Hq10 HE Hra Hranges HX HSKc EQ :=
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
let Hm := fresh "Hm" in let Hcs := fresh "Hcs" in
pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite Hq10, unsigned_lit_small in Hcs by lia;
apply (raw_obj_final Ef _ res); [exact Hcs | | exact Hranges];
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in let Hlj := fresh "Hlj" in
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; cbn [length] in Hlj;
rewrite !ew_havoc_old by lia; apply (HX j v Hj)
end ]
end end.
Ltac class_fact HS K lo HE38 :=
add_fact HS 38%nat (mkAF lo K 0); [| ew_strip; rewrite HE38, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
End S.
End u.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
