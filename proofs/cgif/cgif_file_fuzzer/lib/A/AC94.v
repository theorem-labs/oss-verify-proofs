(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw YCbx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91 AC99 AC92 AC9b AC96 AC9j AC9h AC9i AC9c AC9d AC9e Niset.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Section d.
Variables (cx : lzw_acx) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model)
(ly7 : alayout) (S7 : astate) (W7 : world SEGS) (regs0 : bvmap 5 word) (m0 : word -> option byte).
Hypothesis HCX : acx_ok cx.
Hypothesis HRG : acx_ranges cx.
Hypothesis HSEP : acx_seps cx.
Hypothesis HBL : acx_blk (ablocks B ly7 S7) cx.
Hypothesis HTOK : acx_tok cx (ablocks B lyc Sc).
Hypothesis Hzgp : z_gp cx = as_gp B.
Hypothesis Hztp : z_tp cx = as_tp B.
Hypothesis M0 : alzw_slots m0 cx /\ alzw_sslots m0 cx /\ tlzw_frame m0 (z_sp cx) regs0.
Let J (mem : word -> option byte) (md : Model) : Prop := ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem md 7.
Let mr (mem : word -> option byte) : word -> option byte := mrestrict (w_H W7) mem.
Lemma minv : forall mem, aabove_eq cx m0 (mr mem) ->
alzw_slots (mr mem) cx /\ alzw_sslots (mr mem) cx /\ tlzw_frame (mr mem) (z_sp cx) regs0.
Proof.
intros mem HA. destruct M0 as (M1 & M2 & M3). pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & Hsphi & _).
split; [exact (alzw_slots_kept _ _ _ M1 HA Hsphi)|]. split; [exact (alzw_sslots_kept _ _ _ M2 HA Hsphi) | exact (tlzw_frame_keptA _ _ _ _ M3 HA Hsphi)].
Qed.
Inductive crawl_res := CR_eidx (X' : lzw_abs) | CR_head (X' : lzw_abs) | CR_exit (X' : lzw_abs).
Definition cr_pc (r : crawl_res) : Z :=
match r with CR_eidx _ => PC_EIDX | CR_head _ => PC_HEAD | CR_exit _ => PC_EPI end.
Definition cr_post (X : lzw_abs) (c' : config) (r : crawl_res) : Prop :=
exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + cr_pc r)) mem' (seg_rom SEGS)) md' /\ J mem' md' /\ aabove_eq cx m0 (mr mem') /\
match r with
| CR_eidx X' => alzw_regs_core regs' cx /\
agen_at (mr mem') cx (la_lp X') (la_dp X') (la_mp X') /\ lzw_inv (z_idl cx) (z_nP cx) X'
| CR_head X' => alzw_regs_head regs' cx /\ agen_at (mr mem') cx (la_lp X') (la_dp X') (la_mp X') /\ atables_at (mr mem') cx X' /\
lzw_inv (z_idl cx) (z_nP cx) X' /\ la_s X < la_s X' < z_nP cx /\ getr regs' 23 = w64 (la_s X')
| CR_exit X' => alzw_regs_head regs' cx /\ agen_at (mr mem') cx (la_lp X') (la_dp X') (la_mp X') /\
lzw_inv (z_idl cx) (z_nP cx) X' /\ la_s X' = z_nP cx
end.
Definition not_eidx (r : crawl_res) : Prop := match r with CR_eidx _ => False | _ => True end.
Lemma tail_cr : forall X memT (c' : config),
aabove_eq cx m0 (mr memT) ->
(exists regs' mem' md' X',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + atail_pc cx X')) mem' (seg_rom SEGS)) md' /\ J mem' md' /\
aabove_eq cx (mr memT) (mr mem') /\ atail_post cx X regs' (mr mem') X') ->
exists r, cr_post X c' r /\ not_eidx r.
Proof.
intros X memT c' HA (regs' & mem' & md' & X' & -> & HJ' & HA' & (HFH & HG & HT & HI & H24 & Hs)).
unfold atail_pc. destruct (Z.ltb_spec (la_s X') (z_nP cx)) as [Hlt | Hge].
- exists (CR_head X'). split; [|exact I]. exists regs', mem', md'. split; [reflexivity|]. split; [exact HJ'|].
split; [exact (aabove_eq_trans _ _ _ _ HA HA')|]. repeat (split; [assumption|]). split; [lia | exact H24].
- exists (CR_exit X'). split; [|exact I]. exists regs', mem', md'. split; [reflexivity|]. split; [exact HJ'|].
split; [exact (aabove_eq_trans _ _ _ _ HA HA')|]. repeat (split; [assumption|]). lia.
Qed.
Lemma iset_frame : forall mem mem' X,
(forall a, 0 <= a < 2 ^ 64 -> ~ (z_sp cx - 320 + 8 <= a < z_sp cx - 320 + 56) -> mbyte SEGS (mr mem') a = mbyte SEGS (mr mem) a) ->
agen_at (mr mem) cx (la_lp X) (la_dp X) (la_mp X) -> atables_at (mr mem) cx X -> lzw_inv (z_idl cx) (z_nP cx) X ->
aabove_eq cx (mr mem) (mr mem') /\ agen_at (mr mem') cx (la_lp X) (la_dp X) (la_mp X) /\ atables_at (mr mem') cx X.
Proof.
intros mem mem' X Hfr HG HT HI.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & _).
pose proof HRG as (HR & _). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
split; [intros a Ha; apply Hfr; lia|].
split; [apply (agen_at_frame _ _ _ _ _ _ HG); intros a Ha; apply Hfr; lia|].
eapply (atables_at_frame (mr mem) (mr mem') cx X (fun a => z_sp cx - 320 + 8 <= a < z_sp cx - 320 + 56));
[exact HT | exact HI | lia | exact HRG | intros a Ha Hna; apply Hfr; [exact Ha | exact Hna] | | | |];
cbn beta; intros a Ha; unfold z_tisz, z_tmsz in Ha; lia.
Qed.
Lemma inner_loop : forall (k : nat) X regs memT mdT s1 q,
(Z.to_nat (z_nP cx - s1) <= k)%nat ->
J memT mdT -> alzw_regs_core regs cx -> agen_at (mr memT) cx (la_lp X) (la_dp X) (la_mp X) -> atables_at (mr memT) cx X ->
lzw_inv (z_idl cx) (z_nP cx) X -> tin_pre cx regs s1 q -> la_s X < s1 <= z_nP cx - 1 -> 0 <= q < 4096 -> aabove_eq cx m0 (mr memT) ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_INNER)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists regs' md' o s1' q1,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + tio_pc o)) memT (seg_rom SEGS)) md' /\
J memT md' /\ alzw_regs_core regs' cx /\ s1 <= s1' <= z_nP cx - 1 /\ 0 <= q1 < 4096 /\
tio_post cx X s1' q1 (mr memT) regs' o /\ match o with TIO_cont _ => False | _ => True end).
Proof.
induction k as [|k IH]; intros X regs memT mdT s1 q Hk HJ HF HG HT HI HPRE Hs1 Hq HA; [lia|].
destruct (minv memT HA) as (HSL & HSS & HFR).
eapply SRr_bind.
{ eapply (tinner_iter B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q); eassumption. }
cbv beta. intros W' c' _ (-> & regs' & md' & o & -> & HJ' & HF' & HP).
destruct o as [|q'|q'|c].
2:{
destruct HP as (HPRE' & Hq' & Hs2).
eapply SRr_mono.
{ eapply (IH X regs' memT md' (s1 + 1) q'); try eassumption; lia. }
cbv beta. intros W'' c'' _ (-> & regs'' & md'' & o & s1' & q1 & -> & HJ'' & HF'' & Hs1' & Hq1 & HP' & Ho).
split; [reflexivity|]. exists regs'', md'', o, s1', q1. split; [reflexivity|]. split; [exact HJ''|]. split; [exact HF''|].
split; [lia|]. split; [exact Hq1|]. split; [exact HP' | exact Ho]. }
all: apply SRr_ret; split; [reflexivity|]; exists regs', md'; eexists; exists s1, q;
(split; [reflexivity|]); (split; [exact HJ'|]); (split; [exact HF'|]); (split; [lia|]); (split; [lia|]); (split; [exact HP | exact I]).
Qed.
Lemma crawl_step : forall X regs memT mdT,
J memT mdT -> alzw_regs_head regs cx -> agen_at (mr memT) cx (la_lp X) (la_dp X) (la_mp X) -> atables_at (mr memT) cx X ->
lzw_inv (z_idl cx) (z_nP cx) X -> getr regs 23 = w64 (la_s X) -> la_s X < z_nP cx -> aabove_eq cx m0 (mr memT) ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists r, cr_post X c' r).
Proof.
intros X regs memT mdT HJ HFH HG HT HI H24 Hs HA.
destruct (minv memT HA) as (HSL & HSS & HFR). pose proof HFH as (HFX & H30 & H16). pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
assert (Hdp : la_dp X <= 4096).
{ destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_dp]. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & _). lia. }
Local Ltac weaken X :=
apply (SRr_mono SEGS _ _ (fun W' c' => W' = W7 /\ exists r, cr_post X c' r /\ not_eidx r));
[| cbv beta; let r := fresh "r" in let Hr := fresh "Hr" in intros ? ? _ (-> & r & Hr & _); split; [reflexivity | exists r; exact Hr]].
Local Ltac eidx X regs' memT md' HJ' HA :=
apply SRr_ret; split; [reflexivity|]; exists (CR_eidx X); exists regs', memT, md'; split; [reflexivity|]; split; [exact HJ'|];
split; [exact HA|].
eapply SRr_bind.
{ eapply (thead_seg B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X); eassumption. }
cbv beta. intros W' c' _ (-> & regs' & md' & o & -> & HJ' & HF' & HP).
pose proof (alzw_regs_core_of_fix _ _ HF') as HFC'.
destruct o as [|q|c1 c2|q].
-
eidx X regs' memT md' HJ' HA. split; [exact HFC'|]. split; [exact HG | exact HI].
-
destruct HP as (P23 & P15 & Hq & P30).
weaken X. eapply SRr_mono.
{ eapply (temitc_seg B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs' memT md' regs0 X q); try eassumption. }
cbv beta. intros W'' c'' _ [-> HQ]. split; [reflexivity|]. exact (tail_cr X memT c'' HA HQ).
-
destruct HP as (P23 & P15 & P17 & P11 & P14 & P7 & P30 & Hc1 & Hc2 & HTI0 & Hs1 & HC2).
weaken X. eapply SRr_bind.
{ eapply (ttimiss_seg B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs' memT md' regs0 X c1 c2); try eassumption. }
cbv beta. intros W'' c'' _ (-> & regs'' & mem'' & md'' & X' & full & -> & HJ'' & HA'' & HP').
pose proof (aabove_eq_trans _ _ _ _ HA HA'') as HA2.
destruct full.
+
destruct (minv mem'' HA2) as (HSL2 & HSS2 & HFR2).
eapply SRr_mono.
{ eapply (trst_seg B LAWS AMEMSET true cx lyc Sc W memc mdc ly7 S7 W7 regs'' mem'' md'' regs0 X (la_s X + 1)); try eassumption. }
cbv beta. intros W3 c3 _ [-> HQ]. split; [reflexivity|]. destruct HQ as (regs3 & mem3 & md3 & X3 & E3 & HJ3 & HA3 & HTP & _).
apply (tail_cr X mem'' c3 HA2). exists regs3, mem3, md3, X3. auto.
+ apply SRr_ret. split; [reflexivity|]. apply (tail_cr X memT _ HA). exists regs'', mem'', md'', X'. auto.
-
destruct HP as (P23 & P15 & P7 & P13 & P16 & Hq & Hs2).
eapply SRr_bind.
{ eapply (tisetup_seg B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs' memT md' regs0 X q); try eassumption; lia. }
cbv beta. intros Wi ci _ (-> & regsi & memi & mdi & -> & HJi & Hfri & HV48 & HFi & HPREi).
destruct (iset_frame memT memi X Hfri HG HT HI) as (HAi & HGi & HTi).
pose proof (aabove_eq_trans _ _ _ _ HA HAi) as HA1.
eapply SRr_bind.
{ eapply (inner_loop (Z.to_nat (z_nP cx - (la_s X + 2))) X regsi memi mdi (la_s X + 2) q); try eassumption; try lia. }
cbv beta. intros W'' c'' _ (-> & regs'' & md'' & o & s1' & q1 & -> & HJ'' & HF'' & Hs1' & Hq1 & HP' & Ho).
destruct o as [|q'|q'|c]; [| destruct Ho | |].
+
eidx X regs'' memi md'' HJ'' HA1. split; [exact HF''|]. split; [exact HGi | exact HI].
+ destruct HP' as (P23' & P15' & Hq' & Hs1e & P30').
weaken X. destruct (minv memi HA1) as (HSLi & HSSi & HFRi). eapply SRr_mono.
{ eapply (temitc_seg B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs'' memi md'' regs0 X q'); try eassumption; try lia. }
cbv beta. intros W3 c3 _ [-> HQ]. split; [reflexivity|]. exact (tail_cr X memi c3 HA1 HQ).
+
destruct HP' as (HPRE' & Hc & HC).
destruct (minv memi HA1) as (HSLi & HSSi & HFRi).
assert (HH : tmiss_hyps B cx lyc Sc W memc mdc ly7 S7 W7 regs'' memi md'' regs0 X s1' q1 c).
{ unfold tmiss_hyps. repeat (split; [first [assumption | lia]|]). exact HV48. }
destruct (Z.eq_dec (la_dp X) 4096) as [Hfull | Hnf].
* weaken X. eapply SRr_bind; [eapply (tmiss_full B LAWS); [exact HH | exact Hfull]|].
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HA3 & HPRE3).
pose proof (aabove_eq_trans _ _ _ _ HA1 HA3) as HA2. destruct (minv mem3 HA2) as (HSL3 & HSS3 & HFR3).
eapply SRr_mono.
{ eapply (trst_seg B LAWS AMEMSET false cx lyc Sc W memc mdc ly7 S7 W7 regs3 mem3 md3 regs0 X s1'); try eassumption. }
cbv beta. intros W4 c4 _ [-> HQ]. split; [reflexivity|]. destruct HQ as (regs4 & mem4 & md4 & X4 & E4 & HJ4 & HA4 & HTP & _).
apply (tail_cr X mem3 c4 HA2). exists regs4, mem4, md4, X4. auto.
* destruct (Z.eq_dec (nth (Z.to_nat q1) (la_LM X) 0) 0) as [HLM0 | HLM1].
-- destruct (Z.eq_dec (nth (Z.to_nat q1) (la_LI X) 0) 0) as [HLI0 | HLI1].
++ weaken X. eapply SRr_mono; [eapply (tmiss_first B LAWS); [exact HH | lia | exact HLM0 | exact HLI0]|].
cbv beta. intros W3 c3 _ [-> HQ]. split; [reflexivity|]. destruct HQ as (regs3 & mem3 & md3 & X3 & E3 & HJ3 & HA3 & HTP & _).
apply (tail_cr X memi c3 HA1). exists regs3, mem3, md3, X3. auto.
++ weaken X. eapply SRr_mono; [eapply (tmiss_sw B LAWS AMEMSET); [exact HH | lia | exact HLM0 | exact HLI1 | exact Hzgp | exact Hztp]|].
cbv beta. intros W3 c3 _ [-> HQ]. split; [reflexivity|]. destruct HQ as (regs3 & mem3 & md3 & X3 & E3 & HJ3 & HA3 & HTP & _).
apply (tail_cr X memi c3 HA1). exists regs3, mem3, md3, X3. auto.
-- weaken X. eapply SRr_mono; [eapply (tmiss_map B LAWS); [exact HH | lia | exact HLM1]|].
cbv beta. intros W3 c3 _ [-> HQ]. split; [reflexivity|]. destruct HQ as (regs3 & mem3 & md3 & X3 & E3 & HJ3 & HA3 & HTP & _).
apply (tail_cr X memi c3 HA1). exists regs3, mem3, md3, X3. auto.
Qed.
Lemma crawl_loop : forall (k : nat) X regs memT mdT,
(Z.to_nat (z_nP cx - la_s X) <= k)%nat ->
J memT mdT -> alzw_regs_head regs cx -> agen_at (mr memT) cx (la_lp X) (la_dp X) (la_mp X) -> atables_at (mr memT) cx X ->
lzw_inv (z_idl cx) (z_nP cx) X -> getr regs 23 = w64 (la_s X) -> la_s X < z_nP cx -> aabove_eq cx m0 (mr memT) ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_HEAD)) memT (seg_rom SEGS)) mdT)
(fun W' c' => W' = W7 /\ exists r, cr_post X c' r /\ match r with CR_head _ => False | _ => True end).
Proof.
induction k as [|k IH]; intros X regs memT mdT Hk HJ HF HG HT HI H24 Hs HA; [lia|].
eapply SRr_bind; [eapply (crawl_step X regs memT mdT); eassumption|].
cbv beta. intros W' c' _ (-> & r & HP). destruct r as [X'|X'|X'].
- apply SRr_ret. split; [reflexivity|]. exists (CR_eidx X'). split; [exact HP | exact I].
- destruct HP as (regs' & mem' & md' & -> & HJ' & HA' & HF' & HG' & HT' & HI' & Hs' & P24).
eapply SRr_mono; [eapply (IH X' regs' mem' md'); try eassumption; lia|].
cbv beta. intros W'' c'' _ (-> & r & HP' & Hr). split; [reflexivity|]. exists r. split; [|exact Hr].
destruct HP' as (regs'' & mem'' & md'' & E'' & HJ'' & HA'' & HR). exists regs'', mem'', md''.
split; [exact E''|]. split; [exact HJ''|]. split; [exact HA''|].
destruct r as [X''|X''|X'']; [| destruct Hr |].
+ destruct HR as (R1 & R2 & R3). repeat (split; [assumption|]). exact R3.
+ destruct HR as (R1 & R2 & R3 & R4). repeat (split; [assumption|]). exact R4.
- apply SRr_ret. split; [reflexivity|]. exists (CR_exit X'). split; [exact HP | exact I].
Qed.
End d.
End S.
End b.
End a.
