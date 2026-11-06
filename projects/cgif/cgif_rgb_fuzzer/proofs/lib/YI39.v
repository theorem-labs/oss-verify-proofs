(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03 YI1e YO3m YI3a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
ss_mem ss = YQ0b.mkRegion (Some n) lo hi lo whi cs :: rest ->
lo' <= lo ->
(forall a, bv_unsigned (ew E n) + lo' <= a < bv_unsigned (ew E n) + lo -> writable_at segs (ms_mem ms) a) ->
0 <= bv_unsigned (ew E n) + lo' ->
all_disjoint E (YQ0b.mkRegion (Some n) lo' hi lo' whi cs) rest ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (YQ0b.mkRegion (Some n) lo' hi lo' whi cs :: rest) (ss_resv ss) (ss_facts ss)) ms.
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
End e.
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
Section h. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.


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
End h.
Ltac ew_strip :=
repeat match goal with
| |- context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) by (cbv; lia)
end.
Ltac ew_strip_in H :=
repeat match type of H with
| context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) in H by (cbv; lia)
end.
Section p. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma obj_at_range : forall segs mem a lay vals,
obj_at segs mem a lay vals -> forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ (8 * Z.of_N (snd (nth j lay (0, 8%N)))).
Proof.
intros segs mem a lay. induction lay as [|f lay IH]; intros [|v' vals] H j v Hj; cbn in H; try tauto; [destruct j; discriminate|].
destruct H as [[_ Hr] H]. destruct j as [|j]; cbn in Hj |- *; [injection Hj as <-; exact Hr | exact (IH vals H j v Hj)].
Qed.
End p.
Ltac agree_tac := first [ apply env_agree_refl | apply env_agree_havoc_ge; [cbv; lia | agree_tac] ].
Section q. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Lemma rdn_of_mbyte : forall (m : word -> option byte) n a,
(forall i, 0 <= i < Z.of_nat n -> exists b, mbyte src2segs m (a + i) = Some b) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
exists bs, rdn src2segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
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
Lemma jmemcpy_rd : forall pcm, memcpy_spec src2_msyms pcm ->
forall E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw,
st_ok src2segs E ss ms -> ss_pc ss = pcm -> ss_resv ss = None ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms) mdc ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 src -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
0 <= n -> 0 <= d -> 0 <= src -> d + n < 2 ^ 64 -> src + n < 2 ^ 64 ->
(forall i, 0 <= i < n -> present (ms_mem ms) (d + i)) ->
(forall i, 0 <= i < n -> exists b, mbyte src2segs (ms_mem ms) (src + i) = Some b) ->
(d + n <= src \/ src + n <= d) ->
(forall a, d <= a < d + n -> wr_byte STK sp0 FP (blocks L A) (blocks Lc Ac) a) ->
SR src2segs (mkCfg ms mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 raw mem2 (seg_rom src2segs)) mdc /\
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
getr regs2 10 = Z_to_bv 64 d /\
(forall r, reg_in r MEMCPY_CLOB = false -> getr regs2 r = getr (ms_regs ms) r) /\
(forall x : word, bv_unsigned x < d \/ d + n <= bv_unsigned x -> mem2 x = ms_mem ms x) /\
mem_grows (ms_mem ms) mem2 /\
(forall i, 0 <= i < n -> mbyte src2segs mem2 (d + i) = mbyte src2segs (ms_mem ms) (src + i))).
Proof.
intros pcm HM E ss ms STK sp0 FP L A mem md Lc Ac mdc d src n raw HS Hpc Hrv HJ H10 H11 H12 H1 Hraw
Hn Hd Hs Hdn Hsn Hpd Hps Hdisj HW.
destruct (rdn_of_mbyte (ms_mem ms) (Z.to_nat n) src ltac:(intros i Hi; apply Hps; lia) Hs ltac:(lia)) as (bs & Hbs & Hlen).
pose proof (store_ok_of_present src2_msyms (ms_mem ms) (Z.to_nat n) d ltac:(intros i Hi; apply Hpd; lia) Hd ltac:(lia)) as Hst.
rewrite <- Hlen in Hst.
destruct (HM bs (Z_to_bv 64 d) (Z_to_bv 64 src) (Z_to_bv 64 n) (ms_mem ms) (seg_rom src2segs) (ms_regs ms) H10 H11 H12)
as (regs2 & Hms & Ha0 & Hfr).
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite Hlen. exact Hbs. }
{ exact Hst. }
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite unsigned_lit_small by lia. lia. }
{ rewrite !unsigned_lit_small by lia. lia. }
rewrite (st_ok_mkst src2segs E ss ms HS Hrv), Hpc.
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
intros i Hi. rewrite (wbytes_mbyte src2segs bs (ms_mem ms) d (d + i)) by lia.
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
[Some src2_A_cgif_writecb; None; None; None; None; None; None; None].
Lemma lits_RawConfig_ok : forall g pgct rattr W H sgct loops,
forall j z, nth_error lits_RawConfig j = Some (Some z) ->
nth_error [src2_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some z.
Proof.
intros g pgct rattr W H sgct loops j z Hj. do 8 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
Qed.
Lemma raw_obj_final : forall E mem res g pgct rattr W H sgct loops,
Forall (chunk_ok src2segs E mem res)
(mkChunk 40 (CVal 4 (SLit 6)) :: obj_chunks_gen LAY_RawConfig 32 lits_RawConfig) ->
(forall j v, nth_error [src2_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v -> ew E (32 + j) = Z_to_bv 64 v) ->
(forall j v, nth_error [src2_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v ->
0 <= v < 2 ^ (8 * Z.of_N (snd (nth j LAY_RawConfig (0, 8%N))))) ->
obj_at src2segs mem res LAY_Raw [src2_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops; R_PENDING].
Proof.
intros E mem res g pgct rattr W H sgct loops Hcs HX HR.
eapply (obj_at_of_chunks_gen src2segs E mem res LAY_Raw _ 32 (lits_RawConfig ++ [Some R_PENDING])).
- eapply incl_Forall; [|exact Hcs]. intros c Hc. cbn in Hc. cbn. tauto.
- reflexivity.
- reflexivity.
- intros j v Hj.
assert (Hcase : (j < 8)%nat \/ j = 8%nat \/ (8 < j)%nat) by lia.
destruct Hcase as [Hlt | [-> | Hgt]].
+ assert (Hj8 : nth_error [src2_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] j = Some v).
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
Lemma cgif_obj_of_chunks : forall E mem g gvals,
Forall (chunk_ok src2segs E mem g) (obj_chunks_gen LAY_CGIF 40 lits_CGIF) ->
length gvals = 17%nat ->
nth_error gvals CG_wfn = Some src2_A_writecb -> nth_error gvals CG_file = Some 0 ->
(forall j v, nth_error gvals j = Some v -> ew E (40 + j) = Z_to_bv 64 v) ->
(forall j v, nth_error gvals j = Some v -> 0 <= v < 2 ^ (8 * Z.of_N (snd (nth j LAY_CGIF (0, 8%N))))) ->
obj_at src2segs mem g LAY_CGIF gvals.
Proof.
intros E mem g gvals Hcs Hlen Hwfn Hfile HY HR.
eapply (obj_at_of_chunks_gen src2segs E mem g LAY_CGIF gvals 40 lits_CGIF Hcs eq_refl Hlen).
intros j v Hj. split; [exact (HR j v Hj)|].
pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj. rewrite Hlen in Hlj.
do 17 (try (destruct j as [|j]; [cbn [nth_error lits_CGIF]; first [apply (HY _ _ Hj) | unfold CG_wfn, CG_file in *; congruence] | ])).
lia.
Qed.
Definition ss_rawnew : sstate :=
mkSS src2_A_cgif_raw_newgif sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-RAWNEW_DEPTH) 0 (-RAWNEW_DEPTH) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 40 0 0 (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig) ;
YQ0b.mkRegion (Some 33%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 40 lits_CGIF) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + RAWNEW_STK) (2^63) 4);
(10%nat, mkAF (CEIL_MIN + RAWNEW_STK) (2^63 - 40) 3);
(33%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4);
(38%nat, mkAF 0 65535 0); (35%nat, mkAF 0 (2^32-1) 0); (39%nat, mkAF 0 65535 0) ] [] []).
Theorem src2_cgif_raw_newgif :
forall L A regs mem md (cfgp g pgct rattr W H sgct loops : Z) gvals,
fn_pre src2_msyms MR RAWNEW_STK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 cfgp -> cfgp mod 8 = 0 -> spZ regs <= cfgp -> cfgp + 40 <= 2 ^ 63 ->
obj_at src2segs mem cfgp LAY_RawConfig [src2_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] ->
(forall i, 0 <= i < 40 -> exists b, mbyte src2segs mem (cfgp + i) = Some b) ->
obj_at src2segs mem g LAY_CGIF gvals ->
nth_error gvals CG_wfn = Some src2_A_writecb -> nth_error gvals CG_file = Some 0 ->
In (g, CGIF_SIZE) (blocks L A) ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 src2_A_cgif_raw_newgif) mem (seg_rom src2segs)) md)
(fun c' => exists L' A' regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom src2segs)) md' /\
journal src2_msyms MR RAWNEW_STK (spZ regs) [] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\
((res = 0 /\ blocks L' A' = blocks L A) \/
(res <> 0 /\ sgct <= 256 /\
(exists b1 b2, blocks L' A' = b1 ++ (res, RAW_SIZE) :: b2 /\ blocks L A = b1 ++ b2) /\
obj_at src2segs mem' res LAY_Raw [src2_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops; R_PENDING]))).
Proof.
intros L A regs mem md cfgp g pgct rattr W H sgct loops gvals HPRE Hid Ha0 Hcal Hclo Hchi Hcfg Hcrd Hobj Hwfn Hfile Hgin.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : RAWNEW_STK = 8304) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
assert (HDv : RAWNEW_DEPTH = 144) by reflexivity. assert (HFv : RAWNEW_FRAME = 112) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
destruct (heap_blocks_range src2_msyms MR LAWS L A mem md g CGIF_SIZE HH Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (obj_at_nth src2segs mem cfgp LAY_RawConfig _ 6 _ _ Hcfg eq_refl eq_refl) as [_ Hsg_r]. cbn [snd] in Hsg_r.
pose proof (obj_at_nth src2segs mem cfgp LAY_RawConfig _ 3 _ _ Hcfg eq_refl eq_refl) as [_ Hat_r]. cbn [snd] in Hat_r.
pose proof (obj_at_nth src2segs mem cfgp LAY_RawConfig _ 7 _ _ Hcfg eq_refl eq_refl) as [_ Hlp_r]. cbn [snd] in Hlp_r.
set (cvals := [src2_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops]) in *.
set (E := Ereg regs (map (Z_to_bv 64) cvals ++ (map (Z_to_bv 64) gvals ++ []))).
assert (HE : forall n (r : reg), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (HX : forall j v, nth_error cvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error gvals j = Some v -> ew E (40 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (40 + j)%nat with (32 + (length cvals + j))%nat by (subst cvals; cbn; lia). apply Ereg_vals2. exact Hj. }
assert (HE2 : ew E 2 = getr regs 2) by (apply (HE 2%nat 2%bv); reflexivity).
assert (HE10 : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (HE 10%nat 10%bv eq_refl); exact Ha0).
assert (HE33 : ew E 33 = Z_to_bv 64 g) by (apply (HX 1%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 sgct) by (apply (HX 6%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 rattr) by (apply (HX 3%nat); reflexivity).
assert (HE39 : ew E 39 = Z_to_bv 64 loops) by (apply (HX 7%nat); reflexivity).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (HS : st_ok src2segs E ss_rawnew (mkst regs (Z_to_bv 64 src2_A_cgif_raw_newgif) mem (seg_rom src2segs))).
{ subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack src2segs _ mem 2 (spZ regs)); [rewrite HE2; reflexivity | lia | lia | intros a Ha; apply Hstw; lia].
+ eapply (region_ok_obj_gen src2segs _ mem 10 cfgp); [rewrite HE10; apply unsigned_lit_small; lia | lia | lia | exact Hcfg | reflexivity | | apply lits_RawConfig_ok | intros i Hi; lia].
intros j v Hj. apply (HX j v Hj).
+ eapply (region_ok_obj_gen src2segs _ mem 33 g); [rewrite HE33; apply unsigned_lit_small; lia | lia | lia | exact Hobj | reflexivity | | apply (lits_CGIF_ok gvals Hwfn Hfile) | intros i Hi; lia].
intros j v Hj. apply (HY j v Hj).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE10, HE33, !unsigned_lit_small by lia. unfold spZ in *. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE33, HE38, HE35, HE39, !unsigned_lit_small by lia. unfold spZ in *.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia. }
pose proof (journal_init src2_msyms MR RAWNEW_STK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 src2_A_cgif_raw_newgif) mem (seg_rom src2segs))) in HJ.
jrun LAWS src2tbl_ok HS HJ.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jbranch src2tbl HS.
{
rewrite branch_ltu_U, U_lit, (U_atom _ 38 sgct HE38) in Hc by lia.
jrun LAWS src2tbl_ok HS HJ.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. jreg HS (1%bv:reg) as Hr1. rewrite (HE 1%nat 1%bv eq_refl) in Hr1.
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists L, A, (ms_regs msx), (ms_mem msx), md, 0 end.
rewrite Hr1, Hra. split; [reflexivity|]. split; [exact HJ|]. split; [exact HPR|]. split; [exact Hid|].
split; [exact Hr10|]. left. split; reflexivity. }
rewrite branch_ltu_U, U_lit, (U_atom _ 38 sgct HE38) in Hc by lia.
assert (Hsg : sgct <= 256) by (destruct (Z.ltb_spec 256 sgct); [discriminate | lia]). clear Hc.
jrun_to LAWS src2tbl_ok HS HJ src2_A_malloc.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hr10. jreg HS (2%bv:reg) as Hr2. rewrite HE2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS src2_errno_low IMG (aa_malloc API)) with (n := 48) (spc := spZ regs - RAWNEW_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact Hr10 | lia
| rewrite Hr2; unfold spZ; f_equal; lia | lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & Hres & Hkeep2 & Hhi2). clear HJ.
change (ms_segs src2_msyms) with src2segs in Hkeep2, Hhi2.
jafter_call2 HS 57%nat regs2 mem2 HP2 (-112) [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack src2segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack src2segs _ _ _ 10); [rewrite HE10; apply unsigned_lit_small; lia | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro src2segs _ _ _ 33); [rewrite HE33; apply unsigned_lit_small; lia | exact Hgin | exact Hkeep2 | lia | lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq10. cbn [ms_regs mkst] in Hq10. rewrite Hres10 in Hq10. symmetry in Hq10.
assert (HE2' : ew (havoc E 57 (map (getr regs2) CLOB)) 2 = getr regs 2) by (ew_havoc; exact HE2).
destruct Hres as [[-> Hbl] | (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr)].
{
pin_reg HS (10%bv:reg) 0 Hres10.
jrun LAWS src2tbl_ok HS HJ2.
{ wr_ok_tac. rewrite HE2'. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS (env_agree_havoc_ge 32 57 _ _ _ ltac:(lia) (env_agree_refl _ _)) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10'. jreg HS (1%bv:reg) as Hr1'. rewrite (HE 1%nat 1%bv eq_refl) in Hr1'.
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists L2, A2, (ms_regs msx), (ms_mem msx), md2, 0 end.
cbn [ms_regs ms_mem mkst]. rewrite Hr1', Hra. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HPR|]. split; [exact Hid2|].
split; [exact Hr10'|]. left. split; [reflexivity | exact Hbl]. }
assert (Hbin2 : In (res, 48) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 res 48 HH2 Hbin2 ltac:(lia)) as (Hb0 & Hb1 & _).
add_fact HS 61%nat (mkAF 4096 (CEIL_MAX - 48) 4). 2:{ rewrite Hq10, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
jrun_to LAWS src2tbl_ok HS HJ2 src2_A_memcpy.
{ wr_ok_tac. rewrite HE2'. exact Hspw. }
jreg HS (10%bv:reg) as M10. rewrite Hq10 in M10.
jreg HS (11%bv:reg) as M11. rewrite HE10 in M11.
jreg HS (12%bv:reg) as M12. jreg HS (1%bv:reg) as M1.
assert (Hgc : g + CGIF_SIZE <= res \/ res + 48 <= g).
{ destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, 48) b2 (g, CGIF_SIZE) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hgin)) as [H0|H0]; cbn [fst snd] in H0; lia. }
assert (Hcfg1 : forall i, 0 <= i < 40 -> mbyte src2segs (ms_mem ms1) (cfgp + i) = mbyte src2segs mem (cfgp + i)).
{ intros i Hi. transitivity (mbyte src2segs mem2 (cfgp + i)).
{ unfold mbyte. rewrite (frame_of_win _ _ _ _ _ (spZ regs) (Z_to_bv 64 (cfgp + i)) HF1 eq_refl); [reflexivity | cbn [base_val r_base]; rewrite HE2'; exact Hspw | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia]. }
rewrite (proj1 (Hhi2 (cfgp + i) ltac:(lia) ltac:(lia))).
unfold mbyte. cbn [ms_mem] in HF, HF0.
rewrite (frame_of_win _ _ _ _ _ (spZ regs) (Z_to_bv 64 (cfgp + i)) HF0 eq_refl); [| cbn [base_val r_base]; rewrite HE2; exact Hspw | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia].
rewrite (frame_of_win _ _ _ _ _ (spZ regs) (Z_to_bv 64 (cfgp + i)) HF eq_refl); [reflexivity | cbn [base_val r_base]; rewrite HE2; exact Hspw | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia]. }
eapply SR_bind.
{ eapply (jmemcpy_rd _ src2_memcpy) with (d := res) (src := cfgp) (n := 40);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact M10 | exact M11 | exact M12 | exact M1
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | lia | ].
- intros i Hi. eapply present_grows; [exact HG1|]. apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 res 48 i HH2 Hbin2 ltac:(lia))).
- intros i Hi. cbn [ms_mem].
destruct (Hcrd i Hi) as [b Hb]. exists b. rewrite <- Hb. apply Hcfg1. exact Hi.
- intros a Ha. replace a with (res + (a - res)) by lia. apply (Hwr (blocks L2 A2)); [exact Hbin2 | lia]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcp3).
jafter_stretch HS 73%nat regs3 mem3 (10%bv :: MEMCPY_CLOB) (src2_A_cgif_raw_newgif + 0x54) HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr3. cbn [reg_in] in Hrr |- *. destruct (bv_eqb rr 10); [discriminate | exact Hrr]. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HE10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HE33, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
pose proof HJ3 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw3) & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with YQ0b.mkRegion _ _ _ _ _ ?cs :: ?rest =>
apply (st_ok_widen_head src2segs E1 ss1 ms1 2 (-112) 0 0 cs rest (-144)) in HS end;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| reflexivity | lia
| ew_havoc; rewrite HE2, Hspw; intros a Ha; apply Hstw3; lia
| ew_havoc; rewrite HE2, Hspw; lia
| cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val]; ew_havoc;
rewrite HE2, HE10, HE33, Hspw, !unsigned_lit_small by lia; repeat split; lia ] end.
assert (Hraw3 : obj_at src2segs mem3 res LAY_RawConfig cvals).
{ eapply (obj_at_copy src2segs (ms_mem ms1) mem3 cfgp res LAY_RawConfig cvals 40); [| exact (proj1 LAY_RawConfig_ok) | exact Hcp3].
eapply obj_at_transport_range; [exact Hcfg | exact (proj1 LAY_RawConfig_ok) |]. intros i Hi. apply Hcfg1. exact Hi. }
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_region src2segs E1 ss1 ms1 (YQ0b.mkRegion (Some 61%nat) 0 RAW_SIZE 0 RAW_SIZE (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig))) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity
| eapply (region_ok_obj_gen src2segs _ mem3 61 res); [ew_havoc; rewrite Hq10; apply unsigned_lit_small; lia | lia | lia | exact Hraw3 | reflexivity | intros j v Hj; assert (Hlj : (j < 8)%nat) by (change 8%nat with (length cvals); apply nth_error_Some; rewrite Hj; discriminate); rewrite !ew_havoc_old by lia; apply (HX j v Hj) | apply lits_RawConfig_ok | ]
| cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val];
rewrite !(ew_havoc_old _ 73 _ 61), !(ew_havoc_old _ 73 _ 2), !(ew_havoc_old _ 57 _ 2), !(ew_havoc_old _ 73 _ 10), !(ew_havoc_old _ 57 _ 10), !(ew_havoc_old _ 73 _ 33), !(ew_havoc_old _ 57 _ 33) by lia;
rewrite Hq10, HE2, HE10, HE33, Hspw, !unsigned_lit_small by lia; repeat split; lia ] end.
2:{ intros i Hi. apply (present_writable src2_msyms). cbn [ms_mem].
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem3 md2 res 48 i HH3 Hbin2 ltac:(lia))). }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (src2_A_cgif_raw_newgif + 84)) mem3 (seg_rom src2segs))) in HJ3.
assert (WR : forall E1 cs0 cs1 lo,
ew E1 61 = Z_to_bv 64 res -> ew E1 2 = getr regs 2 -> -RAWNEW_STK <= lo ->
wr_ok E1 [ YQ0b.mkRegion (Some 61%nat) 0 48 0 48 cs0; YQ0b.mkRegion (Some 2%nat) lo 0 lo 0 cs1;
YQ0b.mkRegion (Some 10%nat) 0 40 0 0 (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig);
YQ0b.mkRegion (Some 33%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 40 lits_CGIF) ]
RAWNEW_STK (spZ regs) [] (blocks L A) (blocks L2 A2)).
{ intros E1 cs0 cs1 lo H61 H2' Hlo'.
eapply wr_ok_cons_gen with (k := 61%nat) (b := res); [reflexivity | rewrite H61; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; intros a Ha; replace a with (res + (a - res)) by lia; apply Hwr; [exact Hbin2 | lia] |].
eapply wr_ok_cons_win; [reflexivity | rewrite H2'; exact Hspw | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Hranges.
Ltac finish_ok HS HJ Hq10 HE Hra Hranges HX :=
lazymatch type of Hq10 with ew _ 61 = Z_to_bv 64 ?res =>
lazymatch type of HE with (forall n r, _ -> ew ?E n = getr ?regs r) =>
let HPR := fresh "HPR" in let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS ltac:(agree_tac) ltac:(vm_compute; reflexivity)) as HPR;
(jreg HS (10%bv:reg) as Hr10); ew_strip_in Hr10; rewrite Hq10 in Hr10;
(jreg HS (1%bv:reg) as Hr1); ew_strip_in Hr1; rewrite (HE 1%nat 1%bv eq_refl) in Hr1;
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
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
jrun LAWS src2tbl_ok HS HJ3.
{ wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
Ltac cur_fact HS Hbase Hn :=
lazymatch type of HS with st_ok _ ?Ec _ _ =>
lazymatch type of Hbase with ew _ ?n = ?v => assert (Hn : ew Ec n = v) by (ew_strip; exact Hbase) end end.
jbranch src2tbl HS.
{
cur_fact HS HE38 HE38c. rewrite branch_eq_U, (U_atom _ 38 sgct HE38c), U_lit in Hc by lia.
assert (Hs0 : sgct = 0) by (destruct (Z.eqb_spec sgct 0); [assumption | discriminate]). clear Hc HE38c.
jrun LAWS src2tbl_ok HS HJ3.
{ wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jbranch src2tbl HS; clear Hc.
- jrun LAWS src2tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
finish_ok HS HJ3 Hq10 HE Hra Hranges HX.
- jrun LAWS src2tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
finish_ok HS HJ3 Hq10 HE Hra Hranges HX. }
cur_fact HS HE38 HE38c. rewrite branch_eq_U, (U_atom _ 38 sgct HE38c), U_lit in Hc by lia.
assert (Hs1 : 1 <= sgct) by (destruct (Z.eqb_spec sgct 0); [discriminate | lia]). clear Hc HE38c.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Hgranges.
pose proof (obj_at_length _ _ _ _ _ Hobj) as Hglen. cbn [length LAY_CGIF] in Hglen.
Ltac attr_finish HS HJ WR Hq10 HE HE2 Hra Hranges HX :=
jbranch src2tbl HS; match goal with H : branch_taken _ _ _ = _ |- _ => clear H end;
[ jrun LAWS src2tbl_ok HS HJ; [ wr_norm; apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia] | finish_ok HS HJ Hq10 HE Hra Hranges HX ]
| jrun LAWS src2tbl_ok HS HJ; [ wr_norm; apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia] | finish_ok HS HJ Hq10 HE Hra Hranges HX ] ].
Ltac class_fact HS K lo HE38 :=
add_fact HS 38%nat (mkAF lo K 0); [| ew_strip; rewrite HE38, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
assert (Hcls : sgct = 1 \/ sgct = 2 \/ (3 <= sgct <= 4) \/ (5 <= sgct <= 8) \/ (9 <= sgct <= 16) \/ (17 <= sgct <= 32) \/
(33 <= sgct <= 64) \/ (65 <= sgct <= 128) \/ (129 <= sgct <= 256)) by lia.
destruct Hcls as [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | Hk]]]]]]]].
-
class_fact HS 1 1 HE38.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jreg HS (2%bv:reg) as W2. ew_strip_in W2. rewrite HE2, Hspw in W2.
jreg HS (20%bv:reg) as W20. ew_strip_in W20. rewrite HE33 in W20.
jreg HS (21%bv:reg) as W21. jreg HS (22%bv:reg) as W22.
pose proof (st_ok_reg _ _ _ _ 23%bv HS) as W23. eval_sr_get_in W23.
cur_fact HS HE38 HE38c. erewrite (wdb_count_denot _ sgct 2 6 HE38c) in W23 by lia. clear HE38c.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC : obj_at src2segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by lia; apply (HY j v Hj)
| ] end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (wdb_loop API IMG (Z.to_nat (3 * (2 - sgct))) (3 * (2 - sgct)) _ _ RAWNEW_STK (spZ regs) [] L A _ md L2 A2 md2 g gvals (spZ regs - RAWNEW_FRAME));
[ lia | lia | exact HJ3 | exact HobjC | exact Hwfn | exact Hfile | lia | lia | exact Hg16
| rewrite W2; f_equal; lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | lia | lia | lia
| exact W20 | exact W21 | exact W22 | exact W23 ]. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & HK4 & H21 & H23 & Hout4 & Hgr4).
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let m := eval vm_compute in (ss_mem ssc) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
let rs := constr:(r0 :: trim_lo r1 (-112) :: rest) in
pose proof (st_ok_after_stretch src2segs 85 Ec ssc msc regs4 mem4 rs WDB_EXIT WDB_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl | apply submem_keep; [apply subregion_trim_lo | apply submem_refl]])
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HK4) as HS2;
let rsv := eval vm_compute in rs in change rs with rsv in HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) in
change (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) with ss2 in HS2
end end.
lazymatch type of Hgr4 with mem_grows ?m0 _ =>
assert (Hout4' : forall x : word, bv_unsigned x < spZ regs - RAWNEW_FRAME - 16 \/ spZ regs - RAWNEW_FRAME - 16 + 16 <= bv_unsigned x -> mem4 x = m0 x)
by (intros x Hx; apply Hout4; lia) end.
clear Hout4. rename Hout4' into Hout4.
match type of HS2 with ?P -> _ => assert (HKm : P); [| specialize (HS2 HKm); clear HKm] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
}
clear HS. rename HS2 into HS.
pin_reg HS (21%bv:reg) 0 H21. pin_reg HS (23%bv:reg) 0 H23.
pose proof HJ4 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw4) & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with YQ0b.mkRegion _ _ _ _ _ ?cs :: ?rest =>
apply (st_ok_widen_head src2segs E1 ss1 ms1 2 (-112) 0 0 cs rest (-144)) in HS end;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| reflexivity | lia
| ew_strip; rewrite HE2, Hspw; intros a Ha; apply Hstw4; lia
| ew_strip; rewrite HE2, Hspw; lia
| cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val]; ew_strip;
rewrite Hq10, HE2, HE10, HE33, Hspw, !unsigned_lit_small by lia; repeat split; lia ] end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 WDB_EXIT) mem4 (seg_rom src2segs))) in HJ4.
jrun LAWS src2tbl_ok HS HJ4. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ4 WR Hq10 HE HE2 Hra Hranges HX.
-
class_fact HS 2 2 HE38.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jbranch src2tbl HS.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct = 2) by (destruct (Z.eqb_spec 2 sgct); [lia | discriminate]). clear Hc HE38c.
jrun LAWS src2tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ3 WR Hq10 HE HE2 Hra Hranges HX.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct <> 2) by (destruct (Z.eqb_spec 2 sgct); [discriminate | lia]). clear Hc HE38c.
exfalso. lia.
-
class_fact HS 4 3 HE38.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jbranch src2tbl HS.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct = 4) by (destruct (Z.eqb_spec 4 sgct); [lia | discriminate]). clear Hc HE38c.
jrun LAWS src2tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ3 WR Hq10 HE HE2 Hra Hranges HX.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct <> 4) by (destruct (Z.eqb_spec 4 sgct); [discriminate | lia]). clear Hc HE38c.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jreg HS (2%bv:reg) as W2. ew_strip_in W2. rewrite HE2, Hspw in W2.
jreg HS (20%bv:reg) as W20. ew_strip_in W20. rewrite HE33 in W20.
jreg HS (21%bv:reg) as W21. jreg HS (22%bv:reg) as W22.
pose proof (st_ok_reg _ _ _ _ 23%bv HS) as W23. eval_sr_get_in W23.
cur_fact HS HE38 HE38c. erewrite (wdb_count_denot _ sgct 4 12 HE38c) in W23 by lia. clear HE38c.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC : obj_at src2segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by lia; apply (HY j v Hj)
| ] end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (wdb_loop API IMG (Z.to_nat (3 * (4 - sgct))) (3 * (4 - sgct)) _ _ RAWNEW_STK (spZ regs) [] L A _ md L2 A2 md2 g gvals (spZ regs - RAWNEW_FRAME));
[ lia | lia | exact HJ3 | exact HobjC | exact Hwfn | exact Hfile | lia | lia | exact Hg16
| rewrite W2; f_equal; lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | lia | lia | lia
| exact W20 | exact W21 | exact W22 | exact W23 ]. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & HK4 & H21 & H23 & Hout4 & Hgr4).
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let m := eval vm_compute in (ss_mem ssc) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
let rs := constr:(r0 :: trim_lo r1 (-112) :: rest) in
pose proof (st_ok_after_stretch src2segs 85 Ec ssc msc regs4 mem4 rs WDB_EXIT WDB_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl | apply submem_keep; [apply subregion_trim_lo | apply submem_refl]])
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HK4) as HS2;
let rsv := eval vm_compute in rs in change rs with rsv in HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) in
change (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) with ss2 in HS2
end end.
lazymatch type of Hgr4 with mem_grows ?m0 _ =>
assert (Hout4' : forall x : word, bv_unsigned x < spZ regs - RAWNEW_FRAME - 16 \/ spZ regs - RAWNEW_FRAME - 16 + 16 <= bv_unsigned x -> mem4 x = m0 x)
by (intros x Hx; apply Hout4; lia) end.
clear Hout4. rename Hout4' into Hout4.
match type of HS2 with ?P -> _ => assert (HKm : P); [| specialize (HS2 HKm); clear HKm] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
}
clear HS. rename HS2 into HS.
pin_reg HS (21%bv:reg) 0 H21. pin_reg HS (23%bv:reg) 0 H23.
pose proof HJ4 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw4) & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with YQ0b.mkRegion _ _ _ _ _ ?cs :: ?rest =>
apply (st_ok_widen_head src2segs E1 ss1 ms1 2 (-112) 0 0 cs rest (-144)) in HS end;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| reflexivity | lia
| ew_strip; rewrite HE2, Hspw; intros a Ha; apply Hstw4; lia
| ew_strip; rewrite HE2, Hspw; lia
| cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val]; ew_strip;
rewrite Hq10, HE2, HE10, HE33, Hspw, !unsigned_lit_small by lia; repeat split; lia ] end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 WDB_EXIT) mem4 (seg_rom src2segs))) in HJ4.
jrun LAWS src2tbl_ok HS HJ4. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ4 WR Hq10 HE HE2 Hra Hranges HX.
-
class_fact HS 8 5 HE38.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jbranch src2tbl HS.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct = 8) by (destruct (Z.eqb_spec 8 sgct); [lia | discriminate]). clear Hc HE38c.
jrun LAWS src2tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ3 WR Hq10 HE HE2 Hra Hranges HX.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct <> 8) by (destruct (Z.eqb_spec 8 sgct); [discriminate | lia]). clear Hc HE38c.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jreg HS (2%bv:reg) as W2. ew_strip_in W2. rewrite HE2, Hspw in W2.
jreg HS (20%bv:reg) as W20. ew_strip_in W20. rewrite HE33 in W20.
jreg HS (21%bv:reg) as W21. jreg HS (22%bv:reg) as W22.
pose proof (st_ok_reg _ _ _ _ 23%bv HS) as W23. eval_sr_get_in W23.
cur_fact HS HE38 HE38c. erewrite (wdb_count_denot _ sgct 8 24 HE38c) in W23 by lia. clear HE38c.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC : obj_at src2segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by lia; apply (HY j v Hj)
| ] end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (wdb_loop API IMG (Z.to_nat (3 * (8 - sgct))) (3 * (8 - sgct)) _ _ RAWNEW_STK (spZ regs) [] L A _ md L2 A2 md2 g gvals (spZ regs - RAWNEW_FRAME));
[ lia | lia | exact HJ3 | exact HobjC | exact Hwfn | exact Hfile | lia | lia | exact Hg16
| rewrite W2; f_equal; lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | lia | lia | lia
| exact W20 | exact W21 | exact W22 | exact W23 ]. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & HK4 & H21 & H23 & Hout4 & Hgr4).
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let m := eval vm_compute in (ss_mem ssc) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
let rs := constr:(r0 :: trim_lo r1 (-112) :: rest) in
pose proof (st_ok_after_stretch src2segs 85 Ec ssc msc regs4 mem4 rs WDB_EXIT WDB_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl | apply submem_keep; [apply subregion_trim_lo | apply submem_refl]])
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HK4) as HS2;
let rsv := eval vm_compute in rs in change rs with rsv in HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) in
change (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) with ss2 in HS2
end end.
lazymatch type of Hgr4 with mem_grows ?m0 _ =>
assert (Hout4' : forall x : word, bv_unsigned x < spZ regs - RAWNEW_FRAME - 16 \/ spZ regs - RAWNEW_FRAME - 16 + 16 <= bv_unsigned x -> mem4 x = m0 x)
by (intros x Hx; apply Hout4; lia) end.
clear Hout4. rename Hout4' into Hout4.
match type of HS2 with ?P -> _ => assert (HKm : P); [| specialize (HS2 HKm); clear HKm] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
}
clear HS. rename HS2 into HS.
pin_reg HS (21%bv:reg) 0 H21. pin_reg HS (23%bv:reg) 0 H23.
pose proof HJ4 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw4) & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with YQ0b.mkRegion _ _ _ _ _ ?cs :: ?rest =>
apply (st_ok_widen_head src2segs E1 ss1 ms1 2 (-112) 0 0 cs rest (-144)) in HS end;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| reflexivity | lia
| ew_strip; rewrite HE2, Hspw; intros a Ha; apply Hstw4; lia
| ew_strip; rewrite HE2, Hspw; lia
| cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val]; ew_strip;
rewrite Hq10, HE2, HE10, HE33, Hspw, !unsigned_lit_small by lia; repeat split; lia ] end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 WDB_EXIT) mem4 (seg_rom src2segs))) in HJ4.
jrun LAWS src2tbl_ok HS HJ4. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ4 WR Hq10 HE HE2 Hra Hranges HX.
-
class_fact HS 16 9 HE38.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jbranch src2tbl HS.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct = 16) by (destruct (Z.eqb_spec 16 sgct); [lia | discriminate]). clear Hc HE38c.
jrun LAWS src2tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ3 WR Hq10 HE HE2 Hra Hranges HX.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct <> 16) by (destruct (Z.eqb_spec 16 sgct); [discriminate | lia]). clear Hc HE38c.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jreg HS (2%bv:reg) as W2. ew_strip_in W2. rewrite HE2, Hspw in W2.
jreg HS (20%bv:reg) as W20. ew_strip_in W20. rewrite HE33 in W20.
jreg HS (21%bv:reg) as W21. jreg HS (22%bv:reg) as W22.
pose proof (st_ok_reg _ _ _ _ 23%bv HS) as W23. eval_sr_get_in W23.
cur_fact HS HE38 HE38c. erewrite (wdb_count_denot _ sgct 16 48 HE38c) in W23 by lia. clear HE38c.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC : obj_at src2segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by lia; apply (HY j v Hj)
| ] end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (wdb_loop API IMG (Z.to_nat (3 * (16 - sgct))) (3 * (16 - sgct)) _ _ RAWNEW_STK (spZ regs) [] L A _ md L2 A2 md2 g gvals (spZ regs - RAWNEW_FRAME));
[ lia | lia | exact HJ3 | exact HobjC | exact Hwfn | exact Hfile | lia | lia | exact Hg16
| rewrite W2; f_equal; lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | lia | lia | lia
| exact W20 | exact W21 | exact W22 | exact W23 ]. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & HK4 & H21 & H23 & Hout4 & Hgr4).
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let m := eval vm_compute in (ss_mem ssc) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
let rs := constr:(r0 :: trim_lo r1 (-112) :: rest) in
pose proof (st_ok_after_stretch src2segs 85 Ec ssc msc regs4 mem4 rs WDB_EXIT WDB_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl | apply submem_keep; [apply subregion_trim_lo | apply submem_refl]])
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HK4) as HS2;
let rsv := eval vm_compute in rs in change rs with rsv in HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) in
change (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) with ss2 in HS2
end end.
lazymatch type of Hgr4 with mem_grows ?m0 _ =>
assert (Hout4' : forall x : word, bv_unsigned x < spZ regs - RAWNEW_FRAME - 16 \/ spZ regs - RAWNEW_FRAME - 16 + 16 <= bv_unsigned x -> mem4 x = m0 x)
by (intros x Hx; apply Hout4; lia) end.
clear Hout4. rename Hout4' into Hout4.
match type of HS2 with ?P -> _ => assert (HKm : P); [| specialize (HS2 HKm); clear HKm] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
}
clear HS. rename HS2 into HS.
pin_reg HS (21%bv:reg) 0 H21. pin_reg HS (23%bv:reg) 0 H23.
pose proof HJ4 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw4) & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with YQ0b.mkRegion _ _ _ _ _ ?cs :: ?rest =>
apply (st_ok_widen_head src2segs E1 ss1 ms1 2 (-112) 0 0 cs rest (-144)) in HS end;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| reflexivity | lia
| ew_strip; rewrite HE2, Hspw; intros a Ha; apply Hstw4; lia
| ew_strip; rewrite HE2, Hspw; lia
| cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val]; ew_strip;
rewrite Hq10, HE2, HE10, HE33, Hspw, !unsigned_lit_small by lia; repeat split; lia ] end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 WDB_EXIT) mem4 (seg_rom src2segs))) in HJ4.
jrun LAWS src2tbl_ok HS HJ4. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ4 WR Hq10 HE HE2 Hra Hranges HX.
-
class_fact HS 32 17 HE38.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jbranch src2tbl HS.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct = 32) by (destruct (Z.eqb_spec 32 sgct); [lia | discriminate]). clear Hc HE38c.
jrun LAWS src2tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ3 WR Hq10 HE HE2 Hra Hranges HX.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct <> 32) by (destruct (Z.eqb_spec 32 sgct); [discriminate | lia]). clear Hc HE38c.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jreg HS (2%bv:reg) as W2. ew_strip_in W2. rewrite HE2, Hspw in W2.
jreg HS (20%bv:reg) as W20. ew_strip_in W20. rewrite HE33 in W20.
jreg HS (21%bv:reg) as W21. jreg HS (22%bv:reg) as W22.
pose proof (st_ok_reg _ _ _ _ 23%bv HS) as W23. eval_sr_get_in W23.
cur_fact HS HE38 HE38c. erewrite (wdb_count_denot _ sgct 32 96 HE38c) in W23 by lia. clear HE38c.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC : obj_at src2segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by lia; apply (HY j v Hj)
| ] end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (wdb_loop API IMG (Z.to_nat (3 * (32 - sgct))) (3 * (32 - sgct)) _ _ RAWNEW_STK (spZ regs) [] L A _ md L2 A2 md2 g gvals (spZ regs - RAWNEW_FRAME));
[ lia | lia | exact HJ3 | exact HobjC | exact Hwfn | exact Hfile | lia | lia | exact Hg16
| rewrite W2; f_equal; lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | lia | lia | lia
| exact W20 | exact W21 | exact W22 | exact W23 ]. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & HK4 & H21 & H23 & Hout4 & Hgr4).
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let m := eval vm_compute in (ss_mem ssc) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
let rs := constr:(r0 :: trim_lo r1 (-112) :: rest) in
pose proof (st_ok_after_stretch src2segs 85 Ec ssc msc regs4 mem4 rs WDB_EXIT WDB_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl | apply submem_keep; [apply subregion_trim_lo | apply submem_refl]])
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HK4) as HS2;
let rsv := eval vm_compute in rs in change rs with rsv in HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) in
change (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) with ss2 in HS2
end end.
lazymatch type of Hgr4 with mem_grows ?m0 _ =>
assert (Hout4' : forall x : word, bv_unsigned x < spZ regs - RAWNEW_FRAME - 16 \/ spZ regs - RAWNEW_FRAME - 16 + 16 <= bv_unsigned x -> mem4 x = m0 x)
by (intros x Hx; apply Hout4; lia) end.
clear Hout4. rename Hout4' into Hout4.
match type of HS2 with ?P -> _ => assert (HKm : P); [| specialize (HS2 HKm); clear HKm] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
}
clear HS. rename HS2 into HS.
pin_reg HS (21%bv:reg) 0 H21. pin_reg HS (23%bv:reg) 0 H23.
pose proof HJ4 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw4) & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with YQ0b.mkRegion _ _ _ _ _ ?cs :: ?rest =>
apply (st_ok_widen_head src2segs E1 ss1 ms1 2 (-112) 0 0 cs rest (-144)) in HS end;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| reflexivity | lia
| ew_strip; rewrite HE2, Hspw; intros a Ha; apply Hstw4; lia
| ew_strip; rewrite HE2, Hspw; lia
| cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val]; ew_strip;
rewrite Hq10, HE2, HE10, HE33, Hspw, !unsigned_lit_small by lia; repeat split; lia ] end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 WDB_EXIT) mem4 (seg_rom src2segs))) in HJ4.
jrun LAWS src2tbl_ok HS HJ4. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ4 WR Hq10 HE HE2 Hra Hranges HX.
-
class_fact HS 64 33 HE38.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jbranch src2tbl HS.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct = 64) by (destruct (Z.eqb_spec 64 sgct); [lia | discriminate]). clear Hc HE38c.
jrun LAWS src2tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ3 WR Hq10 HE HE2 Hra Hranges HX.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct <> 64) by (destruct (Z.eqb_spec 64 sgct); [discriminate | lia]). clear Hc HE38c.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jreg HS (2%bv:reg) as W2. ew_strip_in W2. rewrite HE2, Hspw in W2.
jreg HS (20%bv:reg) as W20. ew_strip_in W20. rewrite HE33 in W20.
jreg HS (21%bv:reg) as W21. jreg HS (22%bv:reg) as W22.
pose proof (st_ok_reg _ _ _ _ 23%bv HS) as W23. eval_sr_get_in W23.
cur_fact HS HE38 HE38c. erewrite (wdb_count_denot _ sgct 64 192 HE38c) in W23 by lia. clear HE38c.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC : obj_at src2segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by lia; apply (HY j v Hj)
| ] end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (wdb_loop API IMG (Z.to_nat (3 * (64 - sgct))) (3 * (64 - sgct)) _ _ RAWNEW_STK (spZ regs) [] L A _ md L2 A2 md2 g gvals (spZ regs - RAWNEW_FRAME));
[ lia | lia | exact HJ3 | exact HobjC | exact Hwfn | exact Hfile | lia | lia | exact Hg16
| rewrite W2; f_equal; lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | lia | lia | lia
| exact W20 | exact W21 | exact W22 | exact W23 ]. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & HK4 & H21 & H23 & Hout4 & Hgr4).
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let m := eval vm_compute in (ss_mem ssc) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
let rs := constr:(r0 :: trim_lo r1 (-112) :: rest) in
pose proof (st_ok_after_stretch src2segs 85 Ec ssc msc regs4 mem4 rs WDB_EXIT WDB_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl | apply submem_keep; [apply subregion_trim_lo | apply submem_refl]])
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HK4) as HS2;
let rsv := eval vm_compute in rs in change rs with rsv in HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) in
change (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) with ss2 in HS2
end end.
lazymatch type of Hgr4 with mem_grows ?m0 _ =>
assert (Hout4' : forall x : word, bv_unsigned x < spZ regs - RAWNEW_FRAME - 16 \/ spZ regs - RAWNEW_FRAME - 16 + 16 <= bv_unsigned x -> mem4 x = m0 x)
by (intros x Hx; apply Hout4; lia) end.
clear Hout4. rename Hout4' into Hout4.
match type of HS2 with ?P -> _ => assert (HKm : P); [| specialize (HS2 HKm); clear HKm] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
}
clear HS. rename HS2 into HS.
pin_reg HS (21%bv:reg) 0 H21. pin_reg HS (23%bv:reg) 0 H23.
pose proof HJ4 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw4) & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with YQ0b.mkRegion _ _ _ _ _ ?cs :: ?rest =>
apply (st_ok_widen_head src2segs E1 ss1 ms1 2 (-112) 0 0 cs rest (-144)) in HS end;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| reflexivity | lia
| ew_strip; rewrite HE2, Hspw; intros a Ha; apply Hstw4; lia
| ew_strip; rewrite HE2, Hspw; lia
| cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val]; ew_strip;
rewrite Hq10, HE2, HE10, HE33, Hspw, !unsigned_lit_small by lia; repeat split; lia ] end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 WDB_EXIT) mem4 (seg_rom src2segs))) in HJ4.
jrun LAWS src2tbl_ok HS HJ4. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ4 WR Hq10 HE HE2 Hra Hranges HX.
-
class_fact HS 128 65 HE38.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jbranch src2tbl HS.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct = 128) by (destruct (Z.eqb_spec 128 sgct); [lia | discriminate]). clear Hc HE38c.
jrun LAWS src2tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ3 WR Hq10 HE HE2 Hra Hranges HX.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct <> 128) by (destruct (Z.eqb_spec 128 sgct); [discriminate | lia]). clear Hc HE38c.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jreg HS (2%bv:reg) as W2. ew_strip_in W2. rewrite HE2, Hspw in W2.
jreg HS (20%bv:reg) as W20. ew_strip_in W20. rewrite HE33 in W20.
jreg HS (21%bv:reg) as W21. jreg HS (22%bv:reg) as W22.
pose proof (st_ok_reg _ _ _ _ 23%bv HS) as W23. eval_sr_get_in W23.
cur_fact HS HE38 HE38c. erewrite (wdb_count_denot _ sgct 128 384 HE38c) in W23 by lia. clear HE38c.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC : obj_at src2segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by lia; apply (HY j v Hj)
| ] end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (wdb_loop API IMG (Z.to_nat (3 * (128 - sgct))) (3 * (128 - sgct)) _ _ RAWNEW_STK (spZ regs) [] L A _ md L2 A2 md2 g gvals (spZ regs - RAWNEW_FRAME));
[ lia | lia | exact HJ3 | exact HobjC | exact Hwfn | exact Hfile | lia | lia | exact Hg16
| rewrite W2; f_equal; lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | lia | lia | lia
| exact W20 | exact W21 | exact W22 | exact W23 ]. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & HK4 & H21 & H23 & Hout4 & Hgr4).
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let m := eval vm_compute in (ss_mem ssc) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
let rs := constr:(r0 :: trim_lo r1 (-112) :: rest) in
pose proof (st_ok_after_stretch src2segs 85 Ec ssc msc regs4 mem4 rs WDB_EXIT WDB_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl | apply submem_keep; [apply subregion_trim_lo | apply submem_refl]])
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HK4) as HS2;
let rsv := eval vm_compute in rs in change rs with rsv in HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) in
change (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) with ss2 in HS2
end end.
lazymatch type of Hgr4 with mem_grows ?m0 _ =>
assert (Hout4' : forall x : word, bv_unsigned x < spZ regs - RAWNEW_FRAME - 16 \/ spZ regs - RAWNEW_FRAME - 16 + 16 <= bv_unsigned x -> mem4 x = m0 x)
by (intros x Hx; apply Hout4; lia) end.
clear Hout4. rename Hout4' into Hout4.
match type of HS2 with ?P -> _ => assert (HKm : P); [| specialize (HS2 HKm); clear HKm] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
}
clear HS. rename HS2 into HS.
pin_reg HS (21%bv:reg) 0 H21. pin_reg HS (23%bv:reg) 0 H23.
pose proof HJ4 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw4) & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with YQ0b.mkRegion _ _ _ _ _ ?cs :: ?rest =>
apply (st_ok_widen_head src2segs E1 ss1 ms1 2 (-112) 0 0 cs rest (-144)) in HS end;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| reflexivity | lia
| ew_strip; rewrite HE2, Hspw; intros a Ha; apply Hstw4; lia
| ew_strip; rewrite HE2, Hspw; lia
| cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val]; ew_strip;
rewrite Hq10, HE2, HE10, HE33, Hspw, !unsigned_lit_small by lia; repeat split; lia ] end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 WDB_EXIT) mem4 (seg_rom src2segs))) in HJ4.
jrun LAWS src2tbl_ok HS HJ4. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ4 WR Hq10 HE HE2 Hra Hranges HX.
-
class_fact HS 256 129 HE38.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jbranch src2tbl HS.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct = 256) by (destruct (Z.eqb_spec 256 sgct); [lia | discriminate]). clear Hc HE38c.
jrun LAWS src2tbl_ok HS HJ3. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ3 WR Hq10 HE HE2 Hra Hranges HX.
+ cur_fact HS HE38 HE38c. rewrite branch_eq_U, U_lit, (U_atom _ 38 sgct HE38c) in Hc by lia.
assert (HsK : sgct <> 256) by (destruct (Z.eqb_spec 256 sgct); [discriminate | lia]). clear Hc HE38c.
jrun_to LAWS src2tbl_ok HS HJ3 WDB_HEAD. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
jreg HS (2%bv:reg) as W2. ew_strip_in W2. rewrite HE2, Hspw in W2.
jreg HS (20%bv:reg) as W20. ew_strip_in W20. rewrite HE33 in W20.
jreg HS (21%bv:reg) as W21. jreg HS (22%bv:reg) as W22.
pose proof (st_ok_reg _ _ _ _ 23%bv HS) as W23. eval_sr_get_in W23.
cur_fact HS HE38 HE38c. erewrite (wdb_count_denot _ sgct 256 768 HE38c) in W23 by lia. clear HE38c.
lazymatch type of HS with st_ok _ ?Ec _ ?msc =>
assert (HobjC : obj_at src2segs (ms_mem msc) g LAY_CGIF gvals);
[ pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm; destruct Hm as (_ & Hm & _);
do 3 (apply Forall_inv_tail in Hm); apply Forall_inv in Hm;
unfold region_ok in Hm; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm; destruct Hm as (_ & _ & _ & Hcs);
ew_strip_in Hcs; rewrite HE33, unsigned_lit_small in Hcs by lia;
apply (cgif_obj_of_chunks Ec _ g gvals Hcs Hglen Hwfn Hfile); [| exact Hgranges];
intros j v Hj; pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite Hj; discriminate)) as Hlj; rewrite Hglen in Hlj;
rewrite !ew_havoc_old by lia; apply (HY j v Hj)
| ] end.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (wdb_loop API IMG (Z.to_nat (3 * (256 - sgct))) (3 * (256 - sgct)) _ _ RAWNEW_STK (spZ regs) [] L A _ md L2 A2 md2 g gvals (spZ regs - RAWNEW_FRAME));
[ lia | lia | exact HJ3 | exact HobjC | exact Hwfn | exact Hfile | lia | lia | exact Hg16
| rewrite W2; f_equal; lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | lia | lia | lia
| exact W20 | exact W21 | exact W22 | exact W23 ]. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & HK4 & H21 & H23 & Hout4 & Hgr4).
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let m := eval vm_compute in (ss_mem ssc) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
let rs := constr:(r0 :: trim_lo r1 (-112) :: rest) in
pose proof (st_ok_after_stretch src2segs 85 Ec ssc msc regs4 mem4 rs WDB_EXIT WDB_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl | apply submem_keep; [apply subregion_trim_lo | apply submem_refl]])
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HK4) as HS2;
let rsv := eval vm_compute in rs in change rs with rsv in HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) in
change (ss_after_stretch ssc rsv 85 WDB_CLOB WDB_EXIT) with ss2 in HS2
end end.
lazymatch type of Hgr4 with mem_grows ?m0 _ =>
assert (Hout4' : forall x : word, bv_unsigned x < spZ regs - RAWNEW_FRAME - 16 \/ spZ regs - RAWNEW_FRAME - 16 + 16 <= bv_unsigned x -> mem4 x = m0 x)
by (intros x Hx; apply Hout4; lia) end.
clear Hout4. rename Hout4' into Hout4.
match type of HS2 with ?P -> _ => assert (HKm : P); [| specialize (HS2 HKm); clear HKm] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite Hq10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_strip; rewrite HE33, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
}
clear HS. rename HS2 into HS.
pin_reg HS (21%bv:reg) 0 H21. pin_reg HS (23%bv:reg) 0 H23.
pose proof HJ4 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw4) & _).
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with YQ0b.mkRegion _ _ _ _ _ ?cs :: ?rest =>
apply (st_ok_widen_head src2segs E1 ss1 ms1 2 (-112) 0 0 cs rest (-144)) in HS end;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| reflexivity | lia
| ew_strip; rewrite HE2, Hspw; intros a Ha; apply Hstw4; lia
| ew_strip; rewrite HE2, Hspw; lia
| cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val]; ew_strip;
rewrite Hq10, HE2, HE10, HE33, Hspw, !unsigned_lit_small by lia; repeat split; lia ] end.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
let m := eval vm_compute in (ss_mem ss1) in
lazymatch m with ?ra :: ?rb :: ?rest =>
apply (st_ok_swap01 src2segs E1 ss1 ms1 ra rb rest) in HS; [|reflexivity];
match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end end end.
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 WDB_EXIT) mem4 (seg_rom src2segs))) in HJ4.
jrun LAWS src2tbl_ok HS HJ4. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
attr_finish HS HJ4 WR Hq10 HE HE2 Hra Hranges HX.
Qed.
End S.
End q.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
