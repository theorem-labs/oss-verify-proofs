(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC81.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Definition ffn_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0 0 0) ] [] [].
Definition ss_ffn : sstate := mkSS A_freeFrame sr_atoms [stack_region 32] None ffn_facts.
Definition Bx0 : sv := SLit SB.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma ffn_entry : forall W ly S regs mem md ch,
afn_pre SEGS B FF_STK ly S W regs mem md ch -> getr regs 10 = w64 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_ffn (restrict (w_H W) (mkst regs (Z_to_bv 64 A_freeFrameP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx0 [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch HPRE H10.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : FF_STK = 16416) by reflexivity.
rewrite restrict_mkst_fx. set (E := Eimg (Ereg regs [])). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split; [| constructor].
unfold ss_ffn, A_freeFrameP. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. unfold stack_region, extent_of_region. cbn. exact (conj I I).
- split; [|split; [exact I | exact I]].
cbn [ffn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Hal16 Hslo Hshi H47 Hceil C1 FFS Hstk0. repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Theorem pb_freeFrame_null : forall W ly S regs mem md ch,
afn_pre SEGS B FF_STK ly S W regs mem md ch -> getr regs 10 = w64 0 ->
SRr SEGS W (cfg_at SEGS A_freeFrameP regs mem md)
(fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B FF_STK (spZ regs) [] ly S W mem md [] ly' S' W' mem' md' 0 /\
aregs_preserved regs regs' /\ (ly' = ly /\ S' = S)).
Proof.
intros W ly S regs mem md ch HPRE H10.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
destruct (ffn_entry W ly S regs mem md ch HPRE H10) as [HS0 SHOK].
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS0 ltac:(cbn [ms_regs restrict mkst]; exact H10) eq_refl) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_ffn] in HS.
pose proof (ajournal_init SEGS B FF_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_freeFrameP) with (Z_to_bv 64 A_freeFrameP).
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; reflexivity]].
- cbn [ms_mem]. apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ.
- eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity].
Qed.
Lemma cl_call : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
Lemma region_kept_block_subw : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs b m,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) ->
0 <= lo -> hi <= req_size m -> lo <= wlo -> whi <= hi ->
(forall a, b + lo <= a < b + hi -> ~ inFP FP1 a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs b m HJ1 Hn Hin Hin2 Hlo Hhi Hw1 Hw2 HnF.
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (G2 b m (a - b) Hin Hin2); [lia|].
replace (b + (a - b)) with a by lia. apply HnF. exact Ha.
- intros _. apply (apresent_writable SEGS). destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & HP & _). apply HP. lia.
Qed.
End f.
End e.
End c.
