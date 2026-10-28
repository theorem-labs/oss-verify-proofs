(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m UO3n
YI00 YI02 YI01 YI07 YI03 YI04 YI06 YI5a UI2a UI2b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition temitc_facts : list (nat * afact) :=
[ (10%nat, mkAF 0 4095 0); (22%nat, mkAF 0 99999999 0); (44%nat, mkAF 4096 CEIL_MAX 1) ].
Definition temitc_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 37%nat 0) (SAlu ALU_SLL (SOff 41%nat 0) (SLit 1)), SOff 44%nat 0) ].
Definition temitc_conds : list acond := [ mkAC BC_GEU (SOff 44%nat 0) (SOff 37%nat 0) ].
Definition ss_temitc : sstate := tlzw_ss TPC_EMITC sr_atoms true [regw 44 2] temitc_facts temitc_conds temitc_alias.
Definition ttail_facts : list (nat * afact) := [ (22%nat, mkAF 0 100000000 0) ].
Definition ss_ttail : sstate := tlzw_ss TPC_TAIL sr_atoms false [] ttail_facts [] [].
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Ltac Ucondg := match goal with Hc : branch_taken _ _ _ = _ |- _ => Ucond Hc end.
Lemma temitc_seg : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X q,
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X -> lzw_inv (y_idl cx) (y_nP cx) X ->
getr regs 22 = Z_to_bv 64 (y_nP cx - 1) -> getr regs 10 = Z_to_bv 64 q -> 0 <= q < 4096 ->
la_s X < y_nP cx ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_EMITC) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs' mem' X',
c' = mkCfg (mkst regs' (Z_to_bv 64 TPC_TAIL) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ tabove_eq cx memc mem' /\
ttail_post cx X regs' mem' X').
Proof.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X q
HCX HRG HSEP HBL HWIN HWT HJ HF HG HT HI H22 H10 Hq Hs.
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
assert (Pld : forall i, 0 <= i < 2 -> present memc (y_ld cx + 2 * lp + i)).
{ intros i Hi. replace (y_ld cx + 2 * lp + i) with (y_ld cx + (2 * lp + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx)) (2 * lp + i) HH ltac:(apply HBt; cbv; tauto) ltac:(lia))). }
assert (Pg : forall i, 0 <= i < 72 -> present memc (y_g cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_g cx) 72 i HH ltac:(apply HBt; cbv; tauto) Hi)). }
remember [Z_to_bv 64 (y_ld cx + 2 * lp)] as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
assert (HE44 : ew E 44 = Z_to_bv 64 (y_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 44), (TE_more regs _ _ _ _ more 0), Hmore; reflexivity).
pose proof (TE_sp regs cx lp dp mp more HF) as HE2. pose proof (TE_g regs cx lp dp mp more HF) as HE8.
pose proof (TE_ld regs cx lp dp mp more) as HE37. pose proof (TE_nP regs cx lp dp mp more) as HE39.
pose proof (TE_lp regs cx lp dp mp more) as HE41. pose proof (TE_dp regs cx lp dp mp more) as HE42. pose proof (TE_mp regs cx lp dp mp more) as HE43.
pose proof (TE_ti regs cx lp dp mp more) as HE32. pose proof (TE_lm regs cx lp dp mp more) as HE33.
pose proof (TE_lc regs cx lp dp mp more) as HE34. pose proof (TE_li regs cx lp dp mp more) as HE35.
pose proof (TE_tm regs cx lp dp mp more) as HE36. pose proof (TE_img regs cx lp dp mp more) as HE38.
rewrite <- HE0 in HE2, HE8, HE37, HE39, HE41, HE42, HE43, HE32, HE33, HE34, HE35, HE36, HE38.
assert (HE22 : ew E 22 = Z_to_bv 64 (y_nP cx - 1)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 22%bv 22) by reflexivity; exact H22).
assert (HE10 : ew E 10 = Z_to_bv 64 q) by (rewrite HE0, (TE_reg regs _ _ _ _ more 10%bv 10) by reflexivity; exact H10).
Local Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (tcx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app tcx_tabs fst snd zz_disj y_tisz y_tmsz y_cap cap] in Hs.
assert (HS : st_ok ubs2segs E ss_temitc (mkst regs (Z_to_bv 64 TPC_EMITC) memc (seg_rom ubs2segs))).
{ unfold ss_temitc, tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more memc TPC_EMITC true); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HF.
- exact HG.
- intros _ a Ha. apply (present_writable ubs2_msyms). replace a with (y_g cx + (a - y_g cx)) by lia. apply Pg. lia.
- lia.
- lia.
- lia.
- vm_compute; reflexivity.
- apply Forall_cons; [|apply Forall_nil].
apply (region_ok_regw _ E memc 44 2 (y_ld cx + 2 * lp) HE44); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs2_msyms). apply Pld. exact Ho.
- cbn [all_disjoint app]; unfold extent_disjoint, regw, gen_region; cbn [r_base r_lo r_hi base_val app].
rewrite HE8, HE44, !unsigned_lit_small by lia. split; [septac HSEP 5%nat 6%nat; lia | exact I].
- cbn [pairwise_disjoint all_disjoint app]. split; exact I.
- unfold temitc_facts. cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE10, HE22, HE44, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r. repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
- unfold temitc_conds. cbn [conds_ok]. split; [|exact I].
apply (cond_geu E 44 0 37 0 (y_ld cx + 2 * lp) (y_ld cx) HE44 HE37); lia.
- unfold temitc_alias. cbn [alias_ok]. split; [|exact I].
apply (alias_b2i' E 37 41 44 (y_ld cx) lp HE37 HE41 HE44); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_EMITC) memc (seg_rom ubs2segs))) in HJ.
pose proof (HWT (y_g cx, 72) ltac:(cbv; tauto)) as Wg.
pose proof (HWT (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) ltac:(cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; tauto)) as Wld.
jrun_to LAWS ubs2tbl_ok HS HJ TPC_TAIL.
{ wr_norm.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 8 (y_g cx)); [reflexivity | rewrite HE8; apply unsigned_lit_small; lia | |].
{ cbn [r_wlo r_whi gen_region]. intros a Ha. replace a with (y_g cx + (a - y_g cx)) by lia.
apply (Wg (blocks Lc Ac)); [apply HBt; cbv; tauto | cbn [snd]; lia]. }
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 44 (y_ld cx + 2 * lp)); [reflexivity | rewrite HE44; apply unsigned_lit_small; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi regw]. intros a Ha. replace a with (y_ld cx + (a - y_ld cx)) by lia.
apply (Wld (blocks Lc Ac)); [apply HBt; cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; tauto | cbn [snd]; lia]. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx), (st_typec (y_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R)) end.
split; [reflexivity|]. split; [exact HJ|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs (tcx_extra cx lp dp mp ++ more) TREGS_FIXL HS
ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
lazymatch goal with HF1 : frame_of _ _ _ ?m' |- _ =>
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (y_g cx + 60 <= a < y_g cx + 68) -> ~ (y_ld cx + 2 * lp <= a < y_ld cx + 2 * lp + 2) ->
mbyte ubs2segs m' a = mbyte ubs2segs (ms_mem (mkst regs (Z_to_bv 64 TPC_EMITC) memc (seg_rom ubs2segs))) a)
by (intros a Ha Hn1 Hn2; eapply (tframe_mbyte_list E _ _ _ [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2)] a HF1 Ha);
[ repeat (apply Forall2_cons; [right; cbn [fst snd r_base r_wlo r_whi regw gen_region base_val]; rewrite ?HE8, ?HE44, ?unsigned_lit_small by lia; lia|]); apply Forall2_nil
| cbn; tauto ])
end.
cbn [ms_mem] in Hout.
assert (HT' : ttables_at (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ ?msx => exact msx end)) cx (mkLA TI LM LI TM s lp dp mp Cn R)).
{ eapply (ttables_at_frame _ _ cx (mkLA TI LM LI TM s lp dp mp Cn R) (fun a => (y_g cx + 60 <= a < y_g cx + 68) \/ (y_ld cx + 2 * lp <= a < y_ld cx + 2 * lp + 2)));
[exact HT | exact HI | lia | exact HRG | intros a Ha Hna; apply Hout; [exact Ha | tauto | tauto] | | | |];
cbn beta; intros a Ha; unfold y_tisz, y_tmsz in Ha.
- septac HSEP 0%nat 5%nat. septac HSEP 0%nat 6%nat. lia.
- septac HSEP 1%nat 5%nat. septac HSEP 1%nat 6%nat. lia.
- septac HSEP 3%nat 5%nat. septac HSEP 3%nat 6%nat. lia.
- septac HSEP 4%nat 5%nat. septac HSEP 4%nat 6%nat. lia. }
pose proof (inv_typec (y_idl cx) (y_nP cx) Hidl _ HI ltac:(cbn [la_s]; lia)) as HI'.
split; [intros a Ha; apply Hout; [lia | lia | septac HSEP 5%nat 6%nat; lia]|].
unfold ttail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM st_typec] in *.
split; [apply (tlzw_regs_fix_kept regs); [exact HF | intros r Hr; apply HK; exact Hr]|].
split.
{
pose proof (tst_ok_region_nth E _ _ 0 _ HS eq_refl) as HRg.
assert (G8 : bv_unsigned (ew E 8) = y_g cx) by (rewrite HE8; apply unsigned_lit_small; lia).
destruct HG as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V60 & V64 & V66).
Local Ltac framed V Hout HSEP := intros k Hk; rewrite Hout; [apply V; exact Hk | cbn in Hk; lia | cbn in Hk; lia | septac HSEP 5%nat 6%nat; cbn in Hk; lia].
unfold gen_at. repeat split.
- framed V0 Hout HSEP.
- framed V8 Hout HSEP.
- framed V16 Hout HSEP.
- framed V24 Hout HSEP.
- framed V32 Hout HSEP.
- framed V40 Hout HSEP.
- framed V48 Hout HSEP.
- framed V56 Hout HSEP.
- change 4%nat with (N.to_nat 4). eapply (tval_mem_of_chunk E _ _ 8%nat (y_g cx) 60 4); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia].
cbn [sv_denot]. rewrite HE41, unsigned_lit_small by lia. reflexivity.
- change 2%nat with (N.to_nat 2). eapply (tval_mem_of_chunk E _ _ 8%nat (y_g cx) 64 2); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia].
cbn [sv_denot]. rewrite HE42, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
- change 2%nat with (N.to_nat 2). eapply (tval_mem_of_chunk E _ _ 8%nat (y_g cx) 66 2); [exact HRg | reflexivity | cbv; tauto | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia].
cbn [sv_denot]. rewrite HE43, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
split; [exact HT'|]. split; [exact HI'|]. split; [treg_val HS (22%bv:reg) |]. lia.
Qed.
Lemma ttail_seg : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc lp s' dp mp,
tcx_ok cx -> tcx_ranges cx -> tcx_win STK sp0 cx ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tlzw_regs_fix regs cx -> gen_at memc cx lp dp mp ->
getr regs 22 = Z_to_bv 64 s' ->
0 <= lp <= 134217726 -> 4 <= dp <= 4096 -> 1 <= mp <= 2047 -> 0 <= s' <= y_nP cx ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_TAIL) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 (if s' <? y_nP cx then TPC_HEAD else TPC_EXIT)) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\
(forall x, mem' x = memc x) /\
tlzw_regs_fix regs' cx /\
getr regs' 22 = Z_to_bv 64 s' /\ getr regs' 11 = Z_to_bv 64 (y_nP cx)).
Proof.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc lp s' dp mp
HCX HRG HWIN HJ HF HG H22 Hlp Hdp Hmp Hs.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
destruct HWIN as [W1 W2].
remember (@nil word) as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
pose proof (TE_nP regs cx lp dp mp more) as HE39. rewrite <- HE0 in HE39.
assert (HE22 : ew E 22 = Z_to_bv 64 s') by (rewrite HE0, (TE_reg regs _ _ _ _ more 22%bv 22) by reflexivity; exact H22).
assert (HS : st_ok ubs2segs E ss_ttail (mkst regs (Z_to_bv 64 TPC_TAIL) memc (seg_rom ubs2segs))).
{ unfold ss_ttail, tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more memc TPC_TAIL false); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HF.
- exact HG.
- intros X0. discriminate X0.
- lia.
- lia.
- lia.
- vm_compute; reflexivity.
- apply Forall_nil.
- exact I.
- exact I.
- unfold ttail_facts. cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE22, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- exact I.
- exact I. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_TAIL) memc (seg_rom ubs2segs))) in HJ.
Local Ltac leaf HS HJ HF HE0 :=
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx) end;
split; [first [ rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity | rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity ] |];
split; [exact HJ|]; split; [mem_unchanged_ro|];
let HK := fresh "HK" in
lazymatch type of HE0 with ?E = Ereg ?regs ?ex =>
pose proof (regs_kept_of_st_ok _ _ _ _ regs ex TREGS_FIXL HS
ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK;
split; [apply (tlzw_regs_fix_kept regs); [exact HF | intros r Hr; apply HK; exact Hr]|]
end;
split; [treg_val HS (22%bv:reg) | treg_val HS (11%bv:reg)].
jrun_to LAWS ubs2tbl_ok HS HJ TPC_HEAD; [wr_ok_tac|].
jbranch ubs2tbl HS; Ucondg.
- jrun_to LAWS ubs2tbl_ok HS HJ TPC_HEAD; [wr_ok_tac|]. leaf HS HJ HF HE0.
- jrun_to LAWS ubs2tbl_ok HS HJ TPC_EXIT; [wr_ok_tac|]. leaf HS HJ HF HE0.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
