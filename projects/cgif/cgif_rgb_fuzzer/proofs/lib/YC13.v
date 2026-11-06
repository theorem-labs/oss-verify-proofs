(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC1b YC2q YC2p YC3r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Definition ffn_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0 0 0) ] [] [].
Definition ss_ffn : sstate := mkSS A_freeFrame sr_atoms [stack_region 32] None ffn_facts.
Definition Bx0 : sv := SLit SB.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma ffn_entry : forall W ly S regs mem md ch,
afn_pre trasegs B FF_STK ly S W regs mem md ch -> getr regs 10 = w64 0 ->
st_ok trasegs (Ereg regs []) ss_ffn (restrict (w_H W) (mkst regs (Z_to_bv 64 A_freeFrame) mem (seg_rom trasegs)))
/\ sh_ok trasegs Bx0 [] (Ereg regs []) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch HPRE H10.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : FF_STK = 16416) by reflexivity.
rewrite restrict_mkst_fx. set (E := Ereg regs []).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split; [| constructor].
unfold ss_ffn. apply (entry_st_ok_full trasegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable trasegs). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. unfold stack_region, extent_of_region. cbn. exact (conj I I).
- split; [|split; [exact I | exact I]].
cbn [ffn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Hal16 Hslo Hshi H47 Hceil C1 FFS Hstk0. repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Theorem tra_freeFrame_null : forall W ly S regs mem md ch,
afn_pre trasegs B FF_STK ly S W regs mem md ch -> getr regs 10 = w64 0 ->
SRr trasegs W (cfg_at trasegs A_freeFrame regs mem md)
(fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B FF_STK (spZ regs) [] ly S W mem md [] ly' S' W' mem' md' 0 /\
aregs_preserved regs regs' /\ (ly' = ly /\ S' = S)).
Proof.
intros W ly S regs mem md ch HPRE H10.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct (ffn_entry W ly S regs mem md ch HPRE H10) as [HS0 SHOK].
pose proof (st_ok_pin_reg' trasegs _ _ _ (10%bv : bv 5) 0 HS0 ltac:(cbn [ms_regs restrict mkst]; exact H10) eq_refl) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_ffn] in HS.
pose proof (ajournal_init trasegs B FF_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Ereg regs []) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros n Hn; reflexivity | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_freeFrame) with (Z_to_bv 64 A_freeFrame).
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
rreg HS (1%bv : bv 5) R1.
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; reflexivity]].
- cbn [ms_mem]. apply (ajournal_materialize trasegs B LAWS Hsegs). exact HJ.
- eapply (aregs_preserved_of_st_ok trasegs _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity].
Qed.
Lemma cl_call : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1
(K : alayout -> astate -> world trasegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal trasegs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview trasegs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre trasegs B STK1 lyc Sc W regsc memc mdc ch1 ->
SRr trasegs W (mkCfg (mkst regsc pc memc (seg_rom trasegs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr trasegs W (mkCfg (mkst regsc pc memc (seg_rom trasegs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal trasegs B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at trasegs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub trasegs B LAWS tra_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
Lemma region_kept_block_subw : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs b m,
ajournal trasegs B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) ->
0 <= lo -> hi <= req_size m -> lo <= wlo -> whi <= hi ->
(forall a, b + lo <= a < b + hi -> ~ inFP FP1 a) ->
region_kept trasegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs b m HJ1 Hn Hin Hin2 Hlo Hhi Hw1 Hw2 HnF.
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trasegs). replace a with (b + (a - b)) by lia. apply (G2 b m (a - b) Hin Hin2); [lia|].
replace (b + (a - b)) with a by lia. apply HnF. exact Ha.
- intros _. apply (apresent_writable trasegs). destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin2) as (_ & _ & _ & _ & HP & _). apply HP. lia.
Qed.
End e.
End c.
