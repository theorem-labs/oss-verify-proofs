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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCgi YChv YChx YChw.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section L.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Definition RWDB_CLOB : list (bv 5) := [1; 6; 10; 11; 12; 13; 14; 15; 26; 27]%bv.
Definition RWDB_KEPT : list (bv 5) := [2; 3; 4; 5; 7; 8; 9; 16; 17; 18; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%bv.
Lemma rwdb_clob_kept : forall r : bv 5, reg_in r RWDB_CLOB = false -> r = 0%bv \/ r = 19%bv \/ In r RWDB_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]).
destruct Hin.
Qed.
Definition rwdb_regions : smem :=
[ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 []; YQ0b.mkRegion (Some 9%nat) 168 176 0 0 [YQ0b.mkChunk 168 (CVal 8 (SOff 34 0))]; got_region; bcell_region 33;
YQ0b.mkRegion (Some 20%nat) 0 CGIF_SIZE 0 0
[YQ0b.mkChunk 56 (CVal 8 (SLit A_writecb)); YQ0b.mkChunk 64 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 80 (CVal 8 (SLit 0))] ].
Definition rwdb_facts : facts :=
mkFacts [ (2%nat, mkAF 70368744177664 140737488355328 4); (26%nat, mkAF 1 765 0); (33%nat, mkAF SB SB 0); (20%nat, HPTR 4);
(32%nat, mkAF 0 18446744073709551615 0) ] [] [].
Definition ss_rwdb : sstate :=
mkSS 0x89fec (sr_set (sr_set sr_atoms 19%bv (SLit A_cgif_writecb)) 27%bv (SLit 0)) rwdb_regions None rwdb_facts.
Lemma ra_wdb : forall (m : nat) (n : Z) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k sp1 g ctx bufp,
Z.of_nat m = n ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 2 = Z_to_bv 64 sp1 -> getr regs 9 = Z_to_bv 64 sp1 -> sp1 mod 16 = 0 -> sp0 - STK <= sp1 - 16 -> sp1 <= sp0 -> 70368744177664 + 16 <= sp1 -> sp0 <= 2 ^ 47 ->
getr regs 26 = Z_to_bv 64 n -> 1 <= n <= 765 ->
getr regs 27 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 A_cgif_writecb -> getr regs 20 = Z_to_bv 64 g ->
In (g, CGIF_SIZE) (ablocks B lyc Sc) ->
val_mem trbsegs (mrestrict (w_H W) memc) (g + 56) 8 A_writecb -> val_mem trbsegs (mrestrict (w_H W) memc) (g + 80) 8 0 ->
val_mem trbsegs (mrestrict (w_H W) memc) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 168) 8 bufp -> 0 <= bufp < 2 ^ 64 ->
SRr trbsegs W (mkCfg (mkst regs (Z_to_bv 64 0x89fec) memc (seg_rom trbsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 0x8a00c) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 26 = Z_to_bv 64 0 /\ getr regs' 27 = Z_to_bv 64 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 16 <= a < sp1) -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall r : bv 5, reg_in r RWDB_CLOB = false -> getr regs' r = getr regs r)).
Proof.
induction m as [|m IH]; intros n W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k sp1 g ctx bufp
Hm HJ H2 H9 Hal16 Hlo Hhi H46 H47 H18 Hn H19 H21 H25 Hing M56 M80 M64 Hctx Mbuf Hbufp; [lia|].
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (proj1 HJ) as HAR. pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgpres, Hgh_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (tl_got_shadow _ TL), (tl_shadow_cell _ TL) in Kgot. rewrite (tl_shadow_cell _ TL) in Kcell.
assert (E2 : ew (Ereg regs []) 2 = Z_to_bv 64 sp1) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); exact H2).
assert (E9 : ew (Ereg regs []) 9 = Z_to_bv 64 sp1) by (rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl); exact H9).
assert (E18 : ew (Ereg regs []) 26 = Z_to_bv 64 n) by (rewrite (ew_Ereg_nat regs [] 26 26%bv eq_refl); exact H18).
assert (E25 : ew (Ereg regs []) 20 = Z_to_bv 64 g) by (rewrite (ew_Ereg_nat regs [] 20 20%bv eq_refl); exact H25).
assert (E32 : ew (Ereg regs [Z_to_bv 64 ctx; Z_to_bv 64 SB; Z_to_bv 64 bufp]) 32 = Z_to_bv 64 ctx) by (exact (ew_Ereg_extra regs _ 0)).
assert (E24 : ew (Ereg regs [Z_to_bv 64 ctx; Z_to_bv 64 SB; Z_to_bv 64 bufp]) 33 = Z_to_bv 64 SB) by (exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs [Z_to_bv 64 ctx; Z_to_bv 64 SB; Z_to_bv 64 bufp]) 34 = Z_to_bv 64 bufp) by (exact (ew_Ereg_extra regs _ 2)).
assert (XE : forall n : nat, (n < 32)%nat -> ew (Ereg regs [Z_to_bv 64 ctx; Z_to_bv 64 SB; Z_to_bv 64 bufp]) n = ew (Ereg regs []) n).
{ intros nn Hnn. unfold Ereg. cbn [ew]. destruct (nn <? 32)%nat eqn:Q; [reflexivity|]. apply Nat.ltb_ge in Q. lia. }
rewrite <- (XE 2%nat ltac:(lia)) in E2. rewrite <- (XE 9%nat ltac:(lia)) in E9. rewrite <- (XE 26%nat ltac:(lia)) in E18. rewrite <- (XE 20%nat ltac:(lia)) in E25.
clear XE.
assert (HS : st_ok trbsegs (Ereg regs [Z_to_bv 64 ctx; Z_to_bv 64 SB; Z_to_bv 64 bufp]) ss_rwdb (restrict (w_H W) (mkst regs (Z_to_bv 64 0x89fec) memc (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_rwdb.
eapply (st_ok_pin_reg' trbsegs _ (mkSS 0x89fec (sr_set sr_atoms 19%bv (SLit A_cgif_writecb)) rwdb_regions None rwdb_facts) _ 27%bv 0); [| exact H19 | reflexivity].
eapply (st_ok_pin_reg' trbsegs _ (mkSS 0x89fec sr_atoms rwdb_regions None rwdb_facts) _ 19%bv A_cgif_writecb); [| exact H21 | reflexivity].
apply (rn_st_ok_any (Ereg regs [Z_to_bv 64 ctx; Z_to_bv 64 SB; Z_to_bv 64 bufp]) 0x89fec sr_atoms regs rwdb_regions rwdb_facts (mrestrict (w_H W) memc) (regs_ok_Ereg regs _) eq_refl).
- unfold rwdb_regions, got_region, bcell_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
+ rewrite E2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trbsegs). apply HJpres. lia.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs _ _ sp1 168 8 (SOff 34 0) bufp); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mbuf].
+ unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. rewrite <- (Z.add_0_l 668240) at 1.
apply (chunk_ok_val trbsegs _ _ 0 668240 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) memc _ _ Kgot).
+ unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. rewrite <- (Z.add_0_l 701048) at 1.
apply (chunk_ok_val trbsegs _ _ 0 701048 8 (SOff 33 0) SB);
[cbn [sv_denot]; rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) memc _ _ Kcell).
+ rewrite E25, unsigned_lit_small by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trbsegs _ _ g 56 8 _ A_writecb); [reflexivity | unfold A_writecb; zside | zside | exact M56]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs _ _ g 64 8 _ ctx); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M64]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs _ _ g 80 8 _ 0); [reflexivity | zside | zside | exact M80]|].
apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold rwdb_regions, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite E2, E9, E25, !unsigned_lit_small by lia.
unfold A_GOT_shadow, A_shadow_glob, CGIF_SIZE. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & _) & _).
repeat split; zone_lia.
- split; [|split; exact I]. cbn [rwdb_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2, E18, E24, E25, E32, !unsigned_lit_small by (unfold SB; lia). change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia. }
pose proof HS as HS0.
remember (Ereg regs [Z_to_bv 64 ctx; Z_to_bv 64 SB; Z_to_bv 64 bufp]) as E eqn:HEdef.
assert (HAE : env_agree 32 (Ereg regs []) E).
{ rewrite HEdef. split; [|reflexivity]. intros nn Hnn. unfold Ereg. cbn [ew]. destruct (nn <? 32)%nat eqn:Q; [reflexivity|]. apply Nat.ltb_ge in Q. lia. }
clear HEdef.
shok_auto SHOK (SOff 33 0) E (mrestrict (w_H W) memc).
aj_run_tok trbtbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1).
all: try (obl_blk HJ E25 E24 Hing).
1: { eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp1 - sp0)); [reflexivity | cbn [ew]; rewrite E2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_ok_tac. }
rename HFr into HFr1. rename HG into HG1. clear HF.
assert (NW : forall Ex rs a, (forall r, In r rs -> YQ0b.r_whi r <= YQ0b.r_wlo r \/ (YQ0b.r_base r = Some 2%nat /\ YQ0b.r_wlo r = -16 /\ YQ0b.r_whi r = 0)) ->
bv_unsigned (ew Ex 2) = sp1 -> ~ (sp1 - 16 <= a < sp1) -> ~ in_wrange Ex rs a).
{ intros Ex rs a Hrs Hsp Hna (r & Hin & Hr). destruct (Hrs r Hin) as [Hro | (Hb & Hwlo & Hwhi)]; [lia|].
rewrite Hb, Hwlo, Hwhi in Hr. cbn [base_val] in Hr. rewrite Hsp in Hr. lia. }
srr_branch_tok trbtbl_lib_ok HS SHOK (SB, SB + 2 ^ 44 - 1).
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub negb] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E18 in Hc. replace (bv_unsigned (Z_to_bv 64 n)) with n in Hc by (symmetry; apply unsigned_lit_small; lia).
rewrite !unsigned_lit_small in Hc by lia.
destruct (Z.eqb_spec (n + -1) 0) as [Hz | Hnz]; [discriminate Hc|]. clear Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1) 0x89fec.
1: { eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp1 - sp0));
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_ok_tac. }
rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (2%bv : bv 5) Q2. rreg HS (9%bv : bv 5) Q9. rreg HS (26%bv : bv 5) Q18. rreg HS (27%bv : bv 5) Q19. rreg HS (19%bv : bv 5) Q21. rreg HS (20%bv : bv 5) Q25.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (Hav : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 16 <= a < sp1) -> aview trbsegs (w_H W) (ms_mem msX) a = aview trbsegs (w_H W) memc a);
[ intros a Ha Hna;
rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha ltac:(apply NW; [intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; first [left; lia | right; repeat split; reflexivity] |]); destruct Hr | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E2; apply unsigned_lit_small; lia | exact Hna]));
cbn [ms_mem];
exact (aview_kept_out _ _ _ _ _ HFr1 a Ha ltac:(apply NW; [intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; first [left; lia | right; repeat split; reflexivity] |]); destruct Hr | rewrite E2; apply unsigned_lit_small; lia | exact Hna]))
| ] end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & _) & _).
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply SRr_mono;
[ eapply (IH (n - 1) W (ms_regs msX) (ms_mem msX) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k sp1 g ctx bufp ltac:(lia) HJ);
[ rewrite Q2; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E2
| rewrite Q9; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E9
| exact Hal16 | exact Hlo | exact Hhi | exact H46 | exact H47
| rewrite Q18; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E18, unsigned_lit_small by lia; f_equal; lia
| lia
| exact Q19 | exact Q21
| rewrite Q25; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E25
| exact Hing
| eapply val_mem_kept; [|exact M56]; intros q Hq; apply Hav; lia
| eapply val_mem_kept; [|exact M80]; intros q Hq; apply Hav; lia
| eapply val_mem_kept; [|exact M64]; intros q Hq; apply Hav; lia
| exact Hctx
| eapply val_mem_kept; [|exact Mbuf]; intros q Hq; apply Hav; lia
| exact Hbufp ]
| ] end.
cbv beta. intros W' c' _ (-> & regs'' & mem'' & md'' & -> & HJ'' & HK18 & HK19 & Hav2 & Hpr2 & Hrg2).
split; [reflexivity|]. exists regs'', mem'', md''.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact HK18|]. split; [exact HK19|].
split; [intros a Ha Hna; rewrite (Hav2 a Ha Hna); apply Hav; [exact Ha | exact Hna]|].
split; [intros a Ha; apply Hpr2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. rewrite (Hrg2 r Hr). cbn [ms_regs].
destruct (rwdb_clob_kept r Hr) as [-> | [-> | Hin]].
+ rewrite (st_ok_reg trbsegs _ _ _ 0%bv HS), (st_ok_reg trbsegs _ _ _ 0%bv HS0). reflexivity.
+ rewrite Q21, H21. reflexivity.
+ exact (regs_kept_of_st_ok trbsegs _ _ _ regs [] RWDB_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity) r Hin).
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub negb] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E18 in Hc. replace (bv_unsigned (Z_to_bv 64 n)) with n in Hc by (symmetry; apply unsigned_lit_small; lia).
rewrite !unsigned_lit_small in Hc by lia.
destruct (Z.eqb_spec (n + -1) 0) as [Hz | Hnz]; [|discriminate Hc]. clear Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK (SB, SB + 2 ^ 44 - 1) 0x8a00c.
1: { eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp1 - sp0));
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_ok_tac. }
rename HFr into HFr2. rename HG into HG2. clear HF.
rreg HS (26%bv : bv 5) Q18. rreg HS (27%bv : bv 5) Q19. rreg HS (19%bv : bv 5) Q21.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkst (ms_regs ?msX) _ _ _] => exists (ms_regs msX), (ms_mem msX) end. eexists.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite Q18; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E18, unsigned_lit_small by lia; f_equal; lia|].
split; [exact Q19|].
split.
{ intros a Ha Hna. cbn [ms_mem].
rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha ltac:(apply NW; [intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; first [left; lia | right; repeat split; reflexivity] |]); destruct Hr | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E2; apply unsigned_lit_small; lia | exact Hna])).
exact (aview_kept_out _ _ _ _ _ HFr1 a Ha ltac:(apply NW; [intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; first [left; lia | right; repeat split; reflexivity] |]); destruct Hr | rewrite E2; apply unsigned_lit_small; lia | exact Hna])). }
split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha|].
intros r Hr. cbn [ms_regs].
destruct (rwdb_clob_kept r Hr) as [-> | [-> | Hin]].
+ rewrite (st_ok_reg trbsegs _ _ _ 0%bv HS), (st_ok_reg trbsegs _ _ _ 0%bv HS0). reflexivity.
+ rewrite Q21, H21. reflexivity.
+ exact (regs_kept_of_st_ok trbsegs _ _ _ regs [] RWDB_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity) r Hin).
Qed.
End L.
End b.
