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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8j ACbc ACbf ACbd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition WDB_STK : Z := WCB_STK.
Definition WDB_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv.
Definition WDB_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 21; 28; 29; 30; 31]%bv.
Lemma wdb_clob_kept : forall r : bv 5, reg_in r WDB_CLOB = false -> r = 0%bv \/ In r WDB_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Ltac psrr_branch_pi RUNP BR HS :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNP with
| forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
let r := eval vm_compute in (sym_step_pi tpi ss) in
lazymatch r with
| PStop (SR_branch ?c ?a ?b) => apply (BR W E ss ms _ _ c a b HS); clear HS; let Hc := fresh "Hc" in intros Hc HS
| _ => fail "psrr_branch_pi: state is not stuck at a branch:" r
end end
end.
Definition wdb_regions : smem :=
[ YP09.mkRegion (Some 25%nat) 0 CGIF_SIZE 0 0
[YP09.mkChunk 56 (CVal 8 (SOff 32 0)); YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 80 (CVal 8 (SLit 0))] ].
Definition wdb_facts : facts :=
mkFacts [ (2%nat, mkAF 70368744177664 140737488355328 4); (19%nat, mkAF 1 765 0); (25%nat, HPTR 4);
(22%nat, mkAF 0 18446744073709551615 1); (32%nat, mkAF 0 18446744073709551615 0); (33%nat, mkAF 0 18446744073709551615 0) ] [] [].
Definition ss_wdb : sstate := mkSS 0x38c (sr_set sr_atoms 21%bv (SLit 0)) wdb_regions None wdb_facts.
Section L.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables wfn hw : Z.
Hypothesis Rwfn : 0 <= wfn < 2 ^ 64 /\ wfn mod 2 = 0.
Hypothesis Rhw : 0 <= hw < 2 ^ 64 /\ hw mod 2 = 0.
Hypothesis WFN : twcb_spec SEGS B wfn hw.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Lemma rn_wdb : forall (m : nat) (n : Z) W (regs : bvmap 5 word) memc mdc sp1 lyc Sc g ctx ch1,
Z.of_nat m = n ->
ajournal SEGS B WDB_STK sp1 [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0 ->
getr regs 2 = Z_to_bv 64 sp1 -> sp1 mod 16 = 0 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
achain lyc (aview SEGS (w_H W) memc) sp1 (s0Z regs) ch1 ->
getr regs 19 = Z_to_bv 64 n -> 1 <= n <= 765 ->
getr regs 21 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 wfn -> getr regs 25 = Z_to_bv 64 g ->
In (g, CGIF_SIZE) (ablocks B lyc Sc) ->
val_mem SEGS (mrestrict (w_H W) memc) (g + 56) 8 hw -> val_mem SEGS (mrestrict (w_H W) memc) (g + 80) 8 0 ->
val_mem SEGS (mrestrict (w_H W) memc) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x38c)) memc (seg_rom SEGS)) mdc)
(fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x3a8)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B WDB_STK sp1 [] lyc Sc W memc mdc [] ly' S' W' mem' md' 0 /\
Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\
getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 21 = Z_to_bv 64 0 /\
(forall r : bv 5, reg_in r WDB_CLOB = false -> getr regs' r = getr regs r)).
Proof.
induction m as [|m IH]; intros n W regs memc mdc sp1 lyc Sc g ctx ch1
Hm HJ H2 Hal16 Hgp Htp Hch1 H18 Hn H19 H21 H25 Hing M56 M80 M64 Hctx; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (proj1 HJ) as HAR. pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgpres, Hgh_img.
remember (Eimg (Ereg regs [Z_to_bv 64 hw; Z_to_bv 64 ctx])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E3 : ew E 3 = getr regs 3) by (subst E; eimg_low; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; eimg_low; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; eimg_low; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E18 : ew E 19 = Z_to_bv 64 n) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H18).
assert (E21 : ew E 22 = Z_to_bv 64 wfn) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H21).
assert (E25 : ew E 25 = Z_to_bv 64 g) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 hw) by (subst E; eimg_low; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ctx) by (subst E; eimg_low; exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs []) E).
{ subst E. split; [|reflexivity]. intros nn Hnn. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew]. destruct (nn <? 32)%nat eqn:Q; [reflexivity|]. apply Nat.ltb_ge in Q. lia. }
assert (HS1 : st_ok_pi SEGS VAL E (mkSS 0x38c sr_atoms wdb_regions None wdb_facts) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x38c)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
subst E. apply (rn_st_ok_any (Eimg (Ereg regs [Z_to_bv 64 hw; Z_to_bv 64 ctx])) (BASE + 0x38c) sr_atoms regs wdb_regions wdb_facts (mrestrict (w_H W) memc) (regs_ok_Eimg_Ereg regs _) eq_refl).
- unfold wdb_regions.
apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E25, unsigned_lit_small by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS _ _ g 56 8 _ hw); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M56]|].
apply Forall_cons; [apply (chunk_ok_val SEGS _ _ g 64 8 _ ctx); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M64]|].
apply Forall_cons; [apply (chunk_ok_val SEGS _ _ g 80 8 _ 0); [reflexivity | zside | zside | exact M80]|].
apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact (conj I I).
- split; [|split; exact I]. cbn [wdb_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2, E18, E21, E25, E32, E33, !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 1) with 2. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; lia. }
pose proof (st_ok_pi_pin_reg' _ _ _ (21%bv : bv 5) 0 HS1 ltac:(cbn [ms_regs restrict mkst]; exact H19) eq_refl) as HS. clear HS1.
change (mkSS _ _ _ _ _) with ss_wdb in HS.
clear HEdef. pose proof HS as HS0.
paj_run_to_sh RUNTOP HS HJ 0x398; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|]. clear HF HFr HG.
prreg HS (2%bv : bv 5) P2. prreg HS (22%bv : bv 5) P22. prreg HS (8%bv : bv 5) P8.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 0 _ HS eq_refl) as HRr; cbn [ms_mem restrict mkst] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 56 8%N (SOff 32 0) hw HRr ltac:(cbn [sv_denot]; rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vhw;
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 64 8%N (SOff 33 0) ctx HRr ltac:(cbn [sv_denot]; rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 80 8%N (SLit 0) 0 HRr ltac:(cbn [sv_denot]; rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vpf end;
clear HRr;
let pcj := eval vm_compute in (ss_pc ssx) in
let wj := eval vm_compute in (match plookup asan3_1_tpi pcj with Some (PW x) => x | _ => 0 end) in
eapply (SRr_jalr_call_pi (PL:=PL_asan3_1) W Ex ssx _ _ _ wj (1%bv : bv 5) (22%bv : bv 5) wfn HEI HS eq_refl);
[ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | rewrite P22; exact E21 | exact (proj1 Rwfn) | exact (proj2 Rwfn) |] end.
clear HS. intros mat1 ms1 Ems1 HS1.
prreg HS1 (1%bv : bv 5) P1. prreg HS1 (3%bv : bv 5) P3. prreg HS1 (4%bv : bv 5) P4. prreg HS1 (8%bv : bv 5) P8c. prreg HS1 (10%bv : bv 5) P10. prreg HS1 (2%bv : bv 5) P2c.
lazymatch type of HS1 with st_ok _ ?Ex _ _ =>
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ =>
eapply SRr_bind;
[ eapply (aj_call SEGS B LAWS Hsegs W Ex _ msq WDB_STK sp1 [] lyc Sc W memc mdc [] lyc Sc mdq 0
WCB_STK [] 0 0 (ew Ex 2) _ ch1
(fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 0 /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc)) HS1 eq_refl);
[ rewrite Ems1; cbn [ms_mem mkst]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ
| rewrite P2c; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| reflexivity
| rewrite E2; apply unsigned_lit_small; lia
| reflexivity | lia | unfold WCB_STK; lia | unfold WDB_STK, WCB_STK; lia
| rewrite P3, E3; exact Hgp
| rewrite P4, E4; exact Htp
| exact P1 | apply ret_ok_codeptr_v; [lia | reflexivity] | rewrite unsigned_lit_small by lia; lia
| unfold s0Z; rewrite P8c, E8; fold (s0Z regs); rewrite Ems1; cbn [ms_mem mkst]; replace (sp1 + 0) with sp1 by lia;
apply (achain_kept lyc _ _ sp1 _ ch1 sp1 Hch1 ltac:(lia) ltac:(lia) (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))
| intros HPRE1; eapply SRr_mono;
[ pose proof (WFN W lyc Sc _ _ _ ch1 g ctx HPRE1) as HC; unfold cfg_at in HC;
lazymatch type of HS1 with st_ok _ _ ?sse _ => replace (w64 wfn) with (Z_to_bv 64 (ss_pc sse)) in HC by reflexivity end;
eapply HC; [ rewrite P10; exact E25 | exact Hing | | | | exact Hctx ]; rewrite Ems1; cbn [ms_mem mkst]; [exact Vhw | exact Vctx | exact Vpf]
| cbv beta; unfold wcb_post; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK & HPb);
exists ly2, S2, regs2, mem2, md2; split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | split; [exact HK | exact HPb]]]] ]
| intros a (r0 & Hr0 & _); destruct Hr0 ]
| ] end end.
clear P3 P4 P10 Vhw Vctx Vpf P22.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & Ha04 & HPb4).
pose proof (proj1 HJ4) as HAR4.
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPb4 | exact Hing]).
let K := run_K_hi HS1 in
jafter_call_keep_hi HS1 K regs4 (mrestrict (w_H W4) mem4) HP4 [0%nat] HS2.
rewrite Ems1 in HS2, HJc. cbn [ms_mem ms_regs restrict mkst] in HS2, HJc.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ apply Forall_cons; [|apply Forall_nil].
eapply (region_kept_block_sub SEGS B); [exact HJc | cbn [sv_denot]; rewrite E25; apply unsigned_lit_small; lia | exact Hing | exact Hing4 | lia
| change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia | intros aa Haa Hxa; exact (inFP_nil aa Hxa) ]. }
specialize (HS2 HRK). clear HRK. rewrite <- restrict_mkst_fx in HS2.
lazymatch type of HS2 with st_ok_pi _ _ (havoc ?Eo ?K ?ws) _ _ =>
assert (HEIv : img_env VAL A_LIM (havoc Eo K ws)) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]) end.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS2 ltac:(cbn [ms_regs mkst restrict]; exact Ha04) eq_refl) as HS. clear HS2. norm_ss HS.
paj_run_sh RUNP HS HJ4; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|]. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub negb] in Hc.
rewrite ?ew_havoc_old in Hc by (cbv; lia). rewrite E18 in Hc. replace (bv_unsigned (Z_to_bv 64 n)) with n in Hc by (symmetry; apply unsigned_lit_small; lia). rewrite !unsigned_lit_small in Hc by lia.
destruct (Z.eqb_spec (n + -1) 0) as [Hz | Hnz]; [discriminate Hc|]. clear Hc.
paj_run_to_sh RUNTOP HS HJ4 0x38c; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|]. clear HF HFr HG.
prreg HS (2%bv : bv 5) Q2. prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict _ msX) 0 _ HS eq_refl) as HRr; cbn [ms_mem restrict mkst] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 56 8%N (SOff 32 0) hw HRr ltac:(cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as N56;
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 64 8%N (SOff 33 0) ctx HRr ltac:(cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as N64;
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 80 8%N (SLit 0) 0 HRr ltac:(cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as N80 end;
clear HRr end.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (IH (n - 1) W4 (ms_regs msX) (ms_mem msX) mdX sp1 ly4 S4 g ctx ch1 ltac:(lia));
[ eapply (ajournal_sub_init SEGS B WDB_STK sp1 [] lyc Sc W memc mdc [] ly4 S4 W4 _ _ 0 WDB_STK sp1 [] 0); [exact HJ4 | lia | reflexivity | lia | unfold WDB_STK, WCB_STK; lia | lia]
| rewrite Q2; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); exact E2
| exact Hal16
| rewrite Q3; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E3; exact Hgp
| rewrite Q4; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E4; exact Htp
| unfold s0Z; rewrite Q8; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E8; fold (s0Z regs);
pose proof HJ4 as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _) & _);
apply (achain_ly_top lyc ly4); [exact Etop|];
apply (achain_kept lyc _ _ sp1 _ ch1 sp1 Hch1 ltac:(lia) ltac:(lia) (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4))
| rewrite Q19; cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E18, unsigned_lit_small by lia; f_equal; lia
| lia
| exact Q21
| rewrite Q22; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); exact E21
| rewrite Q25; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); exact E25
| exact Hing4 | exact N56 | exact N80 | exact N64 | exact Hctx ]
| ] end.
cbv beta. intros W' c' _ (ly'' & S'' & regs'' & mem'' & md'' & -> & HJ'' & HPb'' & HK18 & HK19 & Hrg).
exists ly'', S'', regs'', mem'', md''. split; [reflexivity|].
split.
{ pose proof (ajournal_sub SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 HJ'' ltac:(lia) ltac:(lia)
ltac:(intros aa (r0 & Hr0 & _); destruct Hr0)) as HJ6.
cbn [app] in HJ6. replace (0 + 0) with 0 in HJ6 by lia. exact HJ6. }
split; [eapply Permutation_trans; [exact HPb'' | exact HPb4]|].
split; [exact HK18|]. split; [exact HK19|].
intros r Hr. rewrite (Hrg r Hr).
lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?K ?ws) _ _ =>
assert (HAEv : env_agree 32 (Ereg regs []) (havoc Eo K ws)) by (apply (env_agree_havoc_ge 32 K); [cbv; lia | exact HAE]) end.
destruct (wdb_clob_kept r Hr) as [-> | Hin].
+ rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok_pi _ _ _ regs [] WDB_KEPT HS HAEv ltac:(vm_compute; reflexivity) r Hin).
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub negb] in Hc.
rewrite E18 in Hc. replace (bv_unsigned (Z_to_bv 64 n)) with n in Hc by (symmetry; apply unsigned_lit_small; lia). rewrite !unsigned_lit_small in Hc by lia.
destruct (Z.eqb_spec (n + -1) 0) as [Hz | Hnz]; [|discriminate Hc]. clear Hc.
paj_run_to_sh RUNTOP HS HJ4 0x3a8; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|]. clear HF HFr HG.
prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21.
lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?K ?ws) _ _ =>
assert (HAEv : env_agree 32 (Ereg regs []) (havoc Eo K ws)) by (apply (env_agree_havoc_ge 32 K); [cbv; lia | exact HAE]) end.
pmkst HS. apply SRr_ret.
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX] => exists ly4, S4, (ms_regs msX), (ms_mem msX), mdX end.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact HPb4|].
split; [rewrite Q19; cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E18, unsigned_lit_small by lia; f_equal; lia|].
split; [exact Q21|].
intros r Hr. destruct (wdb_clob_kept r Hr) as [-> | Hin].
+ rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok_pi _ _ _ regs [] WDB_KEPT HS HAEv ltac:(vm_compute; reflexivity) r Hin).
Qed.
End L.
End e.
End d.
