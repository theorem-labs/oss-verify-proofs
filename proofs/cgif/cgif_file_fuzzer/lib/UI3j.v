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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b UN3c
YI06 UI5b YI09 YI08 YI0t YI0r YI0o YI0s YI6a UI3n UI3o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u UI30.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ttimiss_facts : list (nat * afact) :=
[ (10%nat, mkAF 0 255 0); (14%nat, mkAF 4096 CEIL_MAX 0); (15%nat, mkAF 0 65280 0); (22%nat, mkAF 1 99999999 0);
(44%nat, mkAF 4096 CEIL_MAX 1); (45%nat, mkAF 0 255 0); (46%nat, mkAF 0 65535 0); (47%nat, mkAF 4096 CEIL_MAX 1); (48%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2^64 - 1) 0) ].
Definition ttimiss_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 37%nat 0) (SAlu ALU_SLL (SOff 41%nat 0) (SLit 1)), SOff 44%nat 0);
(SAlu ALU_ADD (SOff 15%nat 0) (SOff 45%nat 0), SOff 46%nat 0);
(SAlu ALU_XOR (SOff 32%nat 0) (SLit (-1)), SOff 48%nat 0);
(SAlu ALU_ADD (SOff 32%nat 0) (SAlu ALU_SLL (SOff 46%nat 0) (SLit 1)), SOff 47%nat 0) ].
Definition ttimiss_conds (full : bool) : list acond :=
[ mkAC BC_GEU (SOff 44%nat 0) (SOff 37%nat 0); mkAC (if full then BC_NE else BC_EQ) (SAlu ALU_SRL (SOff 42%nat 0) (SLit 12)) (SLit 0) ].
Definition timg1_region : YP09.region := YP09.mkRegion (Some 14%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 45%nat 0))].
Definition ttimiss_regions (full : bool) : smem := [ regw 44 2; timg1_region ] ++ (if full then [] else [regw 47 2]).
Definition ss_ttimiss (full : bool) : sstate :=
tlzw_ss TPC_TIMISS (sr_set sr_atoms 13%bv (SOff 32%nat 0)) true (ttimiss_regions full) ttimiss_facts (ttimiss_conds full) ttimiss_alias.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma ttimiss_segV : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X c1 c2 PIX V,
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X -> lzw_inv (y_idl cx) (y_nP cx) X ->
getr regs 22 = Z_to_bv 64 (la_s X + 1) -> getr regs 10 = Z_to_bv 64 c1 ->
getr regs 14 = Z_to_bv 64 (y_img cx + la_s X + 1) -> getr regs 15 = Z_to_bv 64 (c1 * y_idl cx) -> getr regs 13 = Z_to_bv 64 (y_ti cx) ->
0 <= c1 < y_idl cx -> 0 <= c2 < y_idl cx -> nth (Z.to_nat (c1 * y_idl cx + c2)) (la_TI X) 0 = 0 -> la_s X + 1 < y_nP cx ->
val_mem ubs0segs memc (y_img cx + la_s X + 1) 1 c2 ->
vtabs_at memc cx PIX V -> vinv cx PIX X V ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_TIMISS) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists regs' mem' (full : bool),
c' = mkCfg (mkst regs' (Z_to_bv 64 (if full then TPC_RST else TPC_TAIL)) mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ tabove_eq cx memc mem' /\
(if full then trst_pre cx X (la_s X + 1) regs' mem'
else exists X', ttail_post cx X regs' mem' X' /\ X' = st_ti (y_idl cx) X c1 c2 (la_s X)) /\
vtabs_at mem' cx PIX (mkLV (v_LC V) (v_LD V ++ [c1]))).
Proof using IMG LAWS.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X c1 c2 PIX V
HCX HRG HSEP HBL HWIN HWT HJ HF HG HT HI H22 H10 H14 H15 H13 Hc1 Hc2 HTI0 Hs1 HC2 HVT HVI.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HH.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof HRG as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct HBL as [HBt HBi]. destruct HWIN as [W1 W2].
unfold y_tisz, y_tmsz, y_cap, cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
assert (HMRle : y_MR cx <= 26055).
{ assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (y_idl cx) (y_nP cx) (y_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
remember (c1 * y_idl cx + c2) as K eqn:HK0.
assert (HKr : 0 <= c1 * y_idl cx <= 255 * 256).
{ split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]. }
assert (HKlen : (Z.to_nat K < length TI)%nat /\ 2 * K + 2 <= 2 * y_idl cx * y_idl cx).
{ destruct (TI_read (y_idl cx) (y_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) c1 c2 ltac:(lia) HI ltac:(lia) ltac:(lia)) as [T1 _].
cbn [la_TI] in T1. rewrite <- HK0 in T1. split; [exact T1|]. rewrite LenTI in T1.
assert (K < y_idl cx * y_idl cx) by (apply Z2Nat.inj_lt; [lia | nia | exact T1]). nia. }
destruct HKlen as [HKlen HKsz].
assert (Pld : forall i, 0 <= i < 2 -> present memc (y_ld cx + 2 * lp + i)).
{ intros i Hi. replace (y_ld cx + 2 * lp + i) with (y_ld cx + (2 * lp + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx)) (2 * lp + i) HH ltac:(apply HBt; cbv; tauto) ltac:(lia))). }
assert (Pg : forall i, 0 <= i < 72 -> present memc (y_g cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_g cx) 72 i HH ltac:(apply HBt; cbv; tauto) Hi)). }
assert (Pti : forall i, 0 <= i < 2 -> present memc (y_ti cx + 2 * K + i)).
{ intros i Hi. replace (y_ti cx + 2 * K + i) with (y_ti cx + (2 * K + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_ti cx) (2 * y_idl cx * y_idl cx) (2 * K + i) HH ltac:(apply HBt; cbv; tauto) ltac:(lia))). }
remember [Z_to_bv 64 (y_ld cx + 2 * lp); Z_to_bv 64 c2; Z_to_bv 64 K; Z_to_bv 64 (y_ti cx + 2 * K); Z_to_bv 64 (2 ^ 64 - 1 - y_ti cx)] as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
assert (HE44 : ew E 44 = Z_to_bv 64 (y_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 44), (TE_more regs _ _ _ _ more 0), Hmore; reflexivity).
assert (HE45 : ew E 45 = Z_to_bv 64 c2) by (rewrite HE0; change 45%nat with (44 + 1)%nat; rewrite (TE_more regs _ _ _ _ more 1), Hmore; reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 K) by (rewrite HE0; change 46%nat with (44 + 2)%nat; rewrite (TE_more regs _ _ _ _ more 2), Hmore; reflexivity).
assert (HE47 : ew E 47 = Z_to_bv 64 (y_ti cx + 2 * K)) by (rewrite HE0; change 47%nat with (44 + 3)%nat; rewrite (TE_more regs _ _ _ _ more 3), Hmore; reflexivity).
assert (HE48 : ew E 48 = Z_to_bv 64 (2 ^ 64 - 1 - y_ti cx)) by (rewrite HE0; change 48%nat with (44 + 4)%nat; rewrite (TE_more regs _ _ _ _ more 4), Hmore; reflexivity).
pose proof (TE_sp regs cx lp dp mp more HF) as HE2. pose proof (TE_g regs cx lp dp mp more HF) as HE8.
pose proof (TE_ld regs cx lp dp mp more) as HE37. pose proof (TE_nP regs cx lp dp mp more) as HE39.
pose proof (TE_lp regs cx lp dp mp more) as HE41. pose proof (TE_dp regs cx lp dp mp more) as HE42. pose proof (TE_mp regs cx lp dp mp more) as HE43.
pose proof (TE_ti regs cx lp dp mp more) as HE32. pose proof (TE_lm regs cx lp dp mp more) as HE33.
pose proof (TE_lc regs cx lp dp mp more) as HE34. pose proof (TE_li regs cx lp dp mp more) as HE35.
pose proof (TE_tm regs cx lp dp mp more) as HE36. pose proof (TE_img regs cx lp dp mp more) as HE38.
rewrite <- HE0 in HE2, HE8, HE37, HE39, HE41, HE42, HE43, HE32, HE33, HE34, HE35, HE36, HE38.
assert (HE22 : ew E 22 = Z_to_bv 64 (s + 1)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 22%bv 22) by reflexivity; exact H22).
assert (HE10 : ew E 10 = Z_to_bv 64 c1) by (rewrite HE0, (TE_reg regs _ _ _ _ more 10%bv 10) by reflexivity; exact H10).
assert (HE14 : ew E 14 = Z_to_bv 64 (y_img cx + s + 1)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 14%bv 14) by reflexivity; exact H14).
assert (HE15 : ew E 15 = Z_to_bv 64 (c1 * y_idl cx)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 15%bv 15) by reflexivity; exact H15).
Local Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (tcx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app tcx_tabs fst snd zz_disj y_tisz y_tmsz y_cap cap] in Hs.
remember (dp =? 4096) as full eqn:Hfull.
assert (HS : st_ok ubs0segs E (ss_ttimiss full) (mkst regs (Z_to_bv 64 TPC_TIMISS) memc (seg_rom ubs0segs))).
{ unfold ss_ttimiss.
enough (HS0 : st_ok ubs0segs E (tlzw_ss TPC_TIMISS sr_atoms true (ttimiss_regions full) ttimiss_facts (ttimiss_conds full) ttimiss_alias)
(mkst regs (Z_to_bv 64 TPC_TIMISS) memc (seg_rom ubs0segs))).
{ apply (st_ok_set_reg' ubs0segs E _ _ (13%bv:reg) (SOff 32%nat 0) HS0 eq_refl).
cbn [sv_denot ms_regs]. rewrite HE32, unsigned_lit_small, Z.add_0_r by lia. symmetry. exact H13. }
unfold tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more memc TPC_TIMISS true); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HF.
- exact HG.
- intros _ a Ha. apply (present_writable ubs0_msyms). replace a with (y_g cx + (a - y_g cx)) by lia. apply Pg. lia.
- lia.
- lia.
- lia.
- destruct full; vm_compute; reflexivity.
- unfold ttimiss_regions. apply Forall_app. split.
{ apply Forall_cons.
{ apply (region_ok_regw _ E memc 44 2 (y_ld cx + 2 * lp) HE44); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs0_msyms). apply Pld. exact Ho. }
apply Forall_cons; [|apply Forall_nil].
unfold region_ok, timg1_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE14, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC2]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE45, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
destruct full; [apply Forall_nil|]. apply Forall_cons; [|apply Forall_nil].
apply (region_ok_regw _ E memc 47 2 (y_ti cx + 2 * K) HE47); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs0_msyms). apply Pti. exact Ho.
- unfold ttimiss_regions; destruct full; cbn [all_disjoint app]; unfold extent_disjoint, regw, timg1_region, gen_region; cbn [r_base r_lo r_hi base_val app];
rewrite HE8, HE44, HE14, ?HE47, !unsigned_lit_small by lia.
+ split; [septac HSEP 5%nat 6%nat; lia|]. split; [septac HSEP 6%nat 7%nat; lia | exact I].
+ split; [septac HSEP 5%nat 6%nat; lia|]. split; [septac HSEP 6%nat 7%nat; lia|]. split; [septac HSEP 0%nat 6%nat; lia | exact I].
- unfold ttimiss_regions; destruct full; cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, regw, timg1_region; cbn [r_base r_lo r_hi base_val];
rewrite HE44, HE14, ?HE47, !unsigned_lit_small by lia.
+ split; [split; [septac HSEP 5%nat 7%nat; lia | exact I]|]. split; exact I.
+ split; [split; [septac HSEP 5%nat 7%nat; lia | split; [septac HSEP 0%nat 5%nat; lia | exact I]]|].
split; [split; [septac HSEP 0%nat 7%nat; lia | exact I]|]. split; exact I.
- unfold ttimiss_facts. cbn [atoms_ok]. unfold afact_ok, AC, NOTLO. cbn [af_lo af_hi af_al2].
rewrite HE10, HE14, HE15, HE22, HE44, HE45, HE46, HE47, HE48, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r. repeat split; try lia.
+ apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
+ apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists K; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rti3].
- unfold ttimiss_conds. cbn [conds_ok]. split; [|split; [|exact I]].
+ apply (cond_geu E 44 0 37 0 (y_ld cx + 2 * lp) (y_ld cx) HE44 HE37); lia.
+ destruct full.
* apply cond_ne_U. rewrite (U_dpfull12 E 42 dp HE42), <- Hfull, U_SLit by lia. discriminate.
* apply cond_eq_U. rewrite (U_dpfull12 E 42 dp HE42), <- Hfull, U_SLit by lia. reflexivity.
- unfold ttimiss_alias. cbn [alias_ok]. split; [|split; [|split; [|split; [|exact I]]]].
+ apply (alias_b2i' E 37 41 44 (y_ld cx) lp HE37 HE41 HE44); lia.
+ rewrite HK0 in HE46. apply (alias_add E 15 45 46 (c1 * y_idl cx) c2 HE15 HE45 HE46); lia.
+ apply (alias_nimg E 32 48 (y_ti cx) HE32 HE48). lia.
+ apply (alias_b2i' E 32 46 47 (y_ti cx) K HE32 HE46 HE47); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_TIMISS) memc (seg_rom ubs0segs))) in HJ.
pose proof (HWT (y_g cx, 72) ltac:(cbv; tauto)) as Wg.
pose proof (HWT (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) ltac:(cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; tauto)) as Wld.
pose proof (HWT (y_ti cx, 2 * y_idl cx * y_idl cx) ltac:(cbv [tcx_tabs y_tisz In]; unfold y_tisz; tauto)) as Wti.
Local Ltac wr_tac HE8 HE44 HE47 Wg Wld Wti HBt blc :=
wr_norm;
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 8); [reflexivity | rewrite HE8; apply unsigned_lit_small; lia | |];
[ cbn [r_wlo r_whi gen_region]; intros a Ha;
lazymatch goal with |- wr_byte _ _ _ _ _ ?a => lazymatch type of Wg with wtok' _ _ _ _ (?g, _) => replace a with (g + (a - g)) by lia end end;
apply (Wg blc); [apply HBt; cbv; tauto | cbn [snd]; lia] |];
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 44); [reflexivity | rewrite HE44; apply unsigned_lit_small; lia | |];
[ cbn [r_wlo r_whi regw]; intros a Ha;
lazymatch goal with |- wr_byte _ _ _ _ _ ?a => lazymatch type of Wld with wtok' _ _ _ _ (?g, _) => replace a with (g + (a - g)) by lia end end;
apply (Wld blc); [apply HBt; cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; tauto | cbn [snd]; lia] |];
apply wr_ok_cons_ro; [zlit_tac|];
first [ apply wr_ok_nil
| eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 47); [reflexivity | rewrite HE47; apply unsigned_lit_small; lia | | apply wr_ok_nil];
cbn [r_wlo r_whi regw]; intros a Ha;
lazymatch goal with |- wr_byte _ _ _ _ _ ?a => lazymatch type of Wti with wtok' _ _ _ _ (?g, _) => replace a with (g + (a - g)) by lia end end;
apply (Wti blc); [apply HBt; cbv [tcx_tabs y_tisz In]; unfold y_tisz; tauto | cbn [snd]; lia] ].
Local Ltac gen_tac HS HE8 HE41 HE42 HE43 HG Hout HSEP g :=
let HRg := fresh "HRg" in let G8 := fresh "G8" in
lazymatch type of HS with st_ok _ ?E _ _ =>
pose proof (tst_ok_region_nth E _ _ 0 _ HS eq_refl) as HRg;
assert (G8 : bv_unsigned (ew E 8) = g) by (rewrite HE8; apply unsigned_lit_small; lia);
let V0 := fresh "V" in let V8 := fresh "V" in let V16 := fresh "V" in let V24 := fresh "V" in let V32 := fresh "V" in
let V40 := fresh "V" in let V48 := fresh "V" in let V56 := fresh "V" in
destruct HG as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & _);
unfold gen_at; repeat split;
[ intros k Hk; rewrite Hout; [apply V0; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia | septac HSEP 0%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V8; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia | septac HSEP 0%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V16; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia | septac HSEP 0%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V24; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia | septac HSEP 0%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V32; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia | septac HSEP 0%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V40; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia | septac HSEP 0%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V48; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia | septac HSEP 0%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V56; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia | septac HSEP 0%nat 6%nat; cbn in Hk; lia]
| change 4%nat with (N.to_nat 4); eapply (tval_mem_of_chunk E _ _ 8%nat g 60 4); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia];
cbn [sv_denot]; rewrite HE41, unsigned_lit_small by lia; reflexivity
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E _ _ 8%nat g 64 2); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE42, ?Z.add_0_r, unsigned_lit_small by lia; reflexivity
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E _ _ 8%nat g 66 2); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE43, Z.add_0_r, unsigned_lit_small by lia; reflexivity ]
end.
Local Ltac gen_tac2 HS HE8 HE41 HE42 HE43 HG Hout HSEP g :=
let HRg := fresh "HRg" in let G8 := fresh "G8" in
lazymatch type of HS with st_ok _ ?E _ _ =>
pose proof (tst_ok_region_nth E _ _ 0 _ HS eq_refl) as HRg;
assert (G8 : bv_unsigned (ew E 8) = g) by (rewrite HE8; apply unsigned_lit_small; lia);
let V0 := fresh "V" in let V8 := fresh "V" in let V16 := fresh "V" in let V24 := fresh "V" in let V32 := fresh "V" in
let V40 := fresh "V" in let V48 := fresh "V" in let V56 := fresh "V" in
destruct HG as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & _);
unfold gen_at; repeat split;
[ intros k Hk; rewrite Hout; [apply V0; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V8; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V16; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V24; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V32; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V40; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V48; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia]
| intros k Hk; rewrite Hout; [apply V56; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia]
| change 4%nat with (N.to_nat 4); eapply (tval_mem_of_chunk E _ _ 8%nat g 60 4); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia];
cbn [sv_denot]; rewrite HE41, unsigned_lit_small by lia; reflexivity
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E _ _ 8%nat g 64 2); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE42, ?Z.add_0_r, unsigned_lit_small by lia; reflexivity
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E _ _ 8%nat g 66 2); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE43, Z.add_0_r, unsigned_lit_small by lia; reflexivity ]
end.
destruct full.
-
assert (Hdp4096 : dp = 4096) by (symmetry in Hfull; apply Z.eqb_eq in Hfull; exact Hfull).
jrun_to LAWS ubs0tbl_ok HS HJ TPC_RST; [wr_tac HE8 HE44 HE47 Wg Wld Wti HBt (blocks Lc Ac)|].
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx), true end.
split; [reflexivity|]. split; [exact HJ|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs (tcx_extra cx lp dp mp ++ more) TREGS_FIXL HS
ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
lazymatch goal with HF1 : frame_of _ _ _ ?m' |- _ =>
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (y_g cx + 60 <= a < y_g cx + 68) -> ~ (y_ld cx + 2 * lp <= a < y_ld cx + 2 * lp + 2) ->
mbyte ubs0segs m' a = mbyte ubs0segs (ms_mem (mkst regs (Z_to_bv 64 TPC_TIMISS) memc (seg_rom ubs0segs))) a)
by (intros a Ha Hn1 Hn2;
eapply (tframe_mbyte_list E _ _ _ [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2); (0, 0)] a HF1 Ha);
[ repeat (apply Forall2_cons; [first [left; cbn; lia | right; cbn [fst snd r_base r_wlo r_whi regw timg1_region gen_region base_val]; rewrite ?HE8, ?HE44, ?unsigned_lit_small by lia; lia]|]); apply Forall2_nil
| cbn; repeat split; lia ])
end.
cbn [ms_mem] in Hout.
split; [intros a Ha; apply Hout; [lia | lia | septac HSEP 5%nat 6%nat; lia]|].
split; [| eapply (vtabs_emit memc _ cx PIX V (mkLA TI LM LI TM s lp dp mp Cn R) (fun a => (y_g cx + 60 <= a < y_g cx + 68) \/ (y_ld cx + 2 * lp <= a < y_ld cx + 2 * lp + 2)) c1 HVT HVI ltac:(lia));
[ intros a Ha Hna; apply Hout; [exact Ha | tauto | tauto]
| cbn [la_lp]; split; [|split]; intros a Ha; (split; [lia|]); intros [Hw | Hw];
[ septac HSEP 2%nat 6%nat; lia | septac HSEP 2%nat 5%nat; lia | septac HSEP 6%nat 7%nat; lia | septac HSEP 5%nat 7%nat; lia | septac HSEP 5%nat 6%nat; lia | lia ]
| rewrite <- (Z.add_0_r (y_ld cx + 2 * la_lp (mkLA TI LM LI TM s lp dp mp Cn R))); cbn [la_lp]; change 2%nat with (N.to_nat 2);
eapply (tval_mem_of_chunk E _ _ 44%nat); [eapply (tst_ok_region_nth _ _ _ 1 _ HS); reflexivity | reflexivity | cbv; tauto
| rewrite HE44; apply unsigned_lit_small; lia | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE10, Z.add_0_r, unsigned_lit_small by lia; reflexivity
| lia ] ].
unfold trst_pre. cbv beta iota. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split; [apply (tlzw_regs_fix_kept regs); [exact HF | intros r Hr; apply HK; exact Hr]|].
split; [gen_tac2 HS HE8 HE41 HE42 HE43 HG Hout HSEP (y_g cx)|].
split.
{ eapply (ttables_at_frame _ _ cx (mkLA TI LM LI TM s lp dp mp Cn R)
(fun a => (y_g cx + 60 <= a < y_g cx + 68) \/ (y_ld cx + 2 * lp <= a < y_ld cx + 2 * lp + 2)));
[exact HT | exact HI | lia | exact HRG | intros a Ha Hna; apply Hout; [exact Ha | tauto | tauto] | | | |];
cbn beta; intros a Ha'; unfold y_tisz, y_tmsz in Ha'.
- septac HSEP 0%nat 5%nat. septac HSEP 0%nat 6%nat. lia.
- septac HSEP 1%nat 5%nat. septac HSEP 1%nat 6%nat. lia.
- septac HSEP 3%nat 5%nat. septac HSEP 3%nat 6%nat. lia.
- septac HSEP 4%nat 5%nat. septac HSEP 4%nat 6%nat. lia. }
split; [exact HI|]. split; [exact Hdp4096|]. split; [treg_val HS (22%bv:reg)|]. lia.
-
assert (Hdplt : dp < 4096) by (symmetry in Hfull; apply Z.eqb_neq in Hfull; lia).
jrun_to LAWS ubs0tbl_ok HS HJ TPC_TAIL; [wr_tac HE8 HE44 HE47 Wg Wld Wti HBt (blocks Lc Ac)|].
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx), false end.
split; [reflexivity|]. split; [exact HJ|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs (tcx_extra cx lp dp mp ++ more) TREGS_FIXL HS
ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
lazymatch goal with HF1 : frame_of _ _ _ ?m' |- _ =>
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (y_g cx + 60 <= a < y_g cx + 68) -> ~ (y_ld cx + 2 * lp <= a < y_ld cx + 2 * lp + 2) ->
~ (y_ti cx + 2 * K <= a < y_ti cx + 2 * K + 2) ->
mbyte ubs0segs m' a = mbyte ubs0segs (ms_mem (mkst regs (Z_to_bv 64 TPC_TIMISS) memc (seg_rom ubs0segs))) a)
by (intros a Ha Hn1 Hn2 Hn3;
eapply (tframe_mbyte_list E _ _ _ [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2); (0, 0); (y_ti cx + 2 * K, y_ti cx + 2 * K + 2)] a HF1 Ha);
[ repeat (apply Forall2_cons; [first [left; cbn; lia | right; cbn [fst snd r_base r_wlo r_whi regw timg1_region gen_region base_val]; rewrite ?HE8, ?HE44, ?HE47, ?unsigned_lit_small by lia; lia]|]); apply Forall2_nil
| cbn; repeat split; lia ])
end.
cbn [ms_mem] in Hout.
split; [intros a Ha; apply Hout; [lia | lia | septac HSEP 5%nat 6%nat; lia | septac HSEP 0%nat 6%nat; lia]|].
split; [| eapply (vtabs_emit memc _ cx PIX V (mkLA TI LM LI TM s lp dp mp Cn R)
(fun a => (y_g cx + 60 <= a < y_g cx + 68) \/ (y_ld cx + 2 * lp <= a < y_ld cx + 2 * lp + 2) \/ (y_ti cx + 2 * K <= a < y_ti cx + 2 * K + 2)) c1 HVT HVI ltac:(lia));
[ intros a Ha Hna; apply Hout; [exact Ha | tauto | tauto | tauto]
| cbn [la_lp]; split; [|split]; intros a Ha; (split; [lia|]); intros [Hw | [Hw | Hw]];
[ septac HSEP 2%nat 6%nat; lia | septac HSEP 2%nat 5%nat; lia | septac HSEP 0%nat 2%nat; lia
| septac HSEP 6%nat 7%nat; lia | septac HSEP 5%nat 7%nat; lia | septac HSEP 0%nat 7%nat; lia
| septac HSEP 5%nat 6%nat; lia | lia | septac HSEP 0%nat 5%nat; lia ]
| rewrite <- (Z.add_0_r (y_ld cx + 2 * la_lp (mkLA TI LM LI TM s lp dp mp Cn R))); cbn [la_lp]; change 2%nat with (N.to_nat 2);
eapply (tval_mem_of_chunk E _ _ 44%nat); [eapply (tst_ok_region_nth _ _ _ 1 _ HS); reflexivity | reflexivity | cbv; tauto
| rewrite HE44; apply unsigned_lit_small; lia | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE10, Z.add_0_r, unsigned_lit_small by lia; reflexivity
| lia ] ].
assert (Vnew : val_mem ubs0segs ltac:(lazymatch type of HS with st_ok _ _ _ ?msx => exact (ms_mem msx) end) (y_ti cx + 2 * K) 2 dp).
{ rewrite <- (Z.add_0_r (y_ti cx + 2 * K)). change 2%nat with (N.to_nat 2).
eapply (tval_mem_of_chunk E _ _ 47%nat); [eapply (tst_ok_region_nth _ _ _ 3 _ HS); reflexivity | reflexivity | cbv; tauto
| rewrite HE47; apply unsigned_lit_small; lia | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia].
cbn [sv_denot]. rewrite HE42, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (HT' : ttables_at ltac:(lazymatch type of HS with st_ok _ _ _ ?msx => exact (ms_mem msx) end) cx
(mkLA (updn TI (Z.to_nat K) dp) LM LI TM s lp dp mp Cn R)).
{ destruct HT as (ATI & ALM & ALI & ATM). split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- eapply arr16_upd; [exact ATI | lia | exact HKlen | lia | exact Vnew |].
intros a Ha Hna. rewrite LenTI, Z2Nat.id in Ha by lia.
apply Hout; [lia | septac HSEP 0%nat 6%nat; lia | septac HSEP 0%nat 5%nat; lia | exact Hna].
- eapply arr16_frame; [exact ALM|]. intros a Ha. rewrite LenLM in Ha. cbn in Ha.
apply Hout; [lia | septac HSEP 1%nat 6%nat; lia | septac HSEP 1%nat 5%nat; lia | septac HSEP 0%nat 1%nat; lia].
- eapply arr16_frame; [exact ALI|]. intros a Ha. rewrite LenLI in Ha. cbn in Ha.
apply Hout; [lia | septac HSEP 3%nat 6%nat; lia | septac HSEP 3%nat 5%nat; lia | septac HSEP 0%nat 3%nat; lia].
- eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia.
apply Hout; [lia | septac HSEP 4%nat 6%nat; lia | septac HSEP 4%nat 5%nat; lia | septac HSEP 0%nat 4%nat; lia]. }
pose proof (inv_ti (y_idl cx) (y_nP cx) Hidl _ c1 c2 s HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) Hc1 Hc2) as HI'.
cbn [st_ti] in HI'. rewrite <- HK0 in HI'.
exists (mkLA (updn TI (Z.to_nat K) dp) LM LI TM (s + 1) (lp + 1) (dp + 1) mp (Cn + 1) R).
split; [| cbn [st_ti]; rewrite <- HK0; reflexivity].
unfold ttail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split; [apply (tlzw_regs_fix_kept regs); [exact HF | intros r Hr; apply HK; exact Hr]|].
split; [gen_tac HS HE8 HE41 HE42 HE43 HG Hout HSEP (y_g cx)|].
split; [exact HT'|]. split; [exact HI'|]. split; [treg_val HS (22%bv:reg)|]. lia.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
