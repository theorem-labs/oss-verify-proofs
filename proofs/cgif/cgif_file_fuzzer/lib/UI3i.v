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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u UI30 UI3c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac inl' := repeat (first [ left; reflexivity | right ]).
Ltac inl := cbv; inl'.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tsw_facts : list (nat * afact) :=
[ (22%nat, mkAF 1 99999999 0); (23%nat, mkAF 0 8190 0); (24%nat, mkAF 4 4095 0); (26%nat, mkAF 0 255 0);
(27%nat, mkAF 0 523776 0); (44%nat, mkAF 0 600000 0); (45%nat, mkAF 4096 CEIL_MAX 1); (46%nat, mkAF 4096 CEIL_MAX 1) ].
Definition tsw_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 27%nat 0) (SOff 26%nat 0), SOff 44%nat 0);
(SAlu ALU_ADD (SOff 36%nat 0) (SAlu ALU_SLL (SOff 44%nat 0) (SLit 1)), SOff 45%nat 0);
(SAlu ALU_ADD (SOff 33%nat 0) (SOff 23%nat 0), SOff 46%nat 0) ].
Definition tsw_conds : list acond :=
[ mkAC BC_GEU (SOff 45%nat 0) (SOff 36%nat 0); mkAC BC_GEU (SOff 46%nat 0) (SOff 33%nat 0);
mkAC BC_NE (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 45%nat 0) (SOff 36%nat 0)) (SLit 0)) (SLit 1)) (SLit 0) ].
Definition ss_tsw2 : sstate := tlzw_ss TPC_SW2 sr_atoms true [regw 45 2; regw 46 2] tsw_facts tsw_conds tsw_alias.
Lemma U_ptrchk0 : forall E np nb p base,
ew E np = Z_to_bv 64 p -> ew E nb = Z_to_bv 64 base -> 0 <= base <= p -> p < 2 ^ 64 ->
U E (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff np 0) (SOff nb 0)) (SLit 0)) (SLit 1)) = 1.
Proof using.
intros E np nb p base Hp Hb Rb Rp.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E np p Hp), (U_atom E nb base Hb) by lia.
replace (p <? base) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite !U_SLit. reflexivity.
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma tsw2_segV : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c PIX V1,
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tsw2_pre cx X s1 q c regs memc ->
vtabs_at memc cx PIX V1 -> length (v_LC V1) = 4096%nat -> length PIX = Z.to_nat (y_nP cx) -> Z.of_nat (length (v_LD V1)) = la_lp X + 1 ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_SW2) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists regs' mem' X',
c' = mkCfg (mkst regs' (Z_to_bv 64 TPC_TAIL) mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ tabove_eq cx memc mem' /\
ttail_post cx X regs' mem' X' /\ la_s X' = s1 /\ X' = vx_switch (y_idl cx) X q c s1 /\ vtabs_at mem' cx PIX V1).
Proof using IMG LAWS.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c PIX V1 HCX HRG HSEP HBL HWIN HWT HJ HPRE HVT LenLC LenPIX LenLD.
destruct X as [TI LM LI TM s lp dp mp Cn R].
destruct HPRE as (HFX & HGA & HT & HI & Hdplt & Hq & HLI1 & HLM0 & Hc & Hs1 & H22 & H23 & H24 & H26 & H27 & H25).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HH.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof HRG as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct HBL as [HBt HBi]. destruct HWIN as [W1 W2].
unfold y_tisz, y_tmsz, y_cap, cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
assert (HMRle : y_MR cx <= 26055).
{ assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (y_idl cx) (y_nP cx) (y_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
destruct (inv_switch (y_idl cx) (y_nP cx) Hidl _ q c (s1 - 1) HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) Hq Hc
ltac:(cbn [la_LI]; exact HLI1) ltac:(cbn [la_LM]; exact HLM0)) as (HIsw & Hrow1 & Hrow0).
cbn [la_mp st_switch] in HIsw, Hrow1, Hrow0.
set (row := (mp - 1) * y_idl cx) in *.
assert (Hrowb : row + c < 2049 * y_idl cx /\ 2049 * y_idl cx <= 2049 * 256 /\ 2 * mp <= 2 * 2047 /\ row <= 2046 * 256).
{ split; [lia|]. split; [apply Z.mul_le_mono_nonneg_l; lia |]. split; [lia|].
apply (Z.le_trans _ (2046 * y_idl cx)); [subst row; apply Z.mul_le_mono_nonneg_r; lia | apply Z.mul_le_mono_nonneg_l; lia]. }
assert (LenTMz : length (zero_range TM (Z.to_nat row) (Z.to_nat (y_idl cx))) = Z.to_nat (2049 * y_idl cx)) by (rewrite zero_range_length; exact LenTM).
assert (HJlen : (Z.to_nat (row + c) < length (zero_range TM (Z.to_nat row) (Z.to_nat (y_idl cx))))%nat).
{ rewrite LenTMz. apply Z2Nat.inj_lt; lia. }
assert (HqLM : (Z.to_nat q < length LM)%nat) by (rewrite LenLM; apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; cbn; lia).
destruct HT as (ATI & ALM & ALI & ATMz). cbn [la_TI la_LM la_LI la_TM] in ATI, ALM, ALI, ATMz.
assert (Pg : forall i, 0 <= i < 72 -> present memc (y_g cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_g cx) 72 i HH ltac:(apply HBt; inl) Hi)). }
assert (Ptmc : forall i, 0 <= i < 2 -> present memc (y_tm cx + 2 * (row + c) + i)).
{ intros i Hi. replace (y_tm cx + 2 * (row + c) + i) with (y_tm cx + (2 * (row + c) + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_tm cx) (4098 * y_idl cx) (2 * (row + c) + i) HH ltac:(apply HBt; inl) ltac:(lia))). }
assert (Plmc : forall i, 0 <= i < 2 -> present memc (y_lm cx + 2 * q + i)).
{ intros i Hi. replace (y_lm cx + 2 * q + i) with (y_lm cx + (2 * q + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_lm cx) 8192 (2 * q + i) HH ltac:(apply HBt; inl) ltac:(lia))). }
remember [Z_to_bv 64 (row + c); Z_to_bv 64 (y_tm cx + 2 * (row + c)); Z_to_bv 64 (y_lm cx + 2 * q)] as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx (lp + 1) dp mp ++ more)) as E eqn:HE0.
assert (HE44 : ew E 44 = Z_to_bv 64 (row + c)) by (rewrite HE0, <- (Nat.add_0_r 44), (TE_more regs _ _ _ _ more 0), Hmore; reflexivity).
assert (HE45 : ew E 45 = Z_to_bv 64 (y_tm cx + 2 * (row + c))) by (rewrite HE0; change 45%nat with (44 + 1)%nat; rewrite (TE_more regs _ _ _ _ more 1), Hmore; reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 (y_lm cx + 2 * q)) by (rewrite HE0; change 46%nat with (44 + 2)%nat; rewrite (TE_more regs _ _ _ _ more 2), Hmore; reflexivity).
pose proof (TE_sp regs cx (lp + 1) dp mp more HFX) as HE2. pose proof (TE_g regs cx (lp + 1) dp mp more HFX) as HE8.
pose proof (TE_lm regs cx (lp + 1) dp mp more) as HE33. pose proof (TE_tm regs cx (lp + 1) dp mp more) as HE36.
pose proof (TE_lp regs cx (lp + 1) dp mp more) as HE41. pose proof (TE_dp regs cx (lp + 1) dp mp more) as HE42. pose proof (TE_mp regs cx (lp + 1) dp mp more) as HE43.
rewrite <- HE0 in HE2, HE8, HE33, HE36, HE41, HE42, HE43.
assert (HE22 : ew E 22 = Z_to_bv 64 s1) by (rewrite HE0, (TE_reg regs _ _ _ _ more 22%bv 22) by reflexivity; exact H22).
assert (HE23 : ew E 23 = Z_to_bv 64 (2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 23%bv 23) by reflexivity; exact H23).
assert (HE24 : ew E 24 = Z_to_bv 64 dp) by (rewrite HE0, (TE_reg regs _ _ _ _ more 24%bv 24) by reflexivity; exact H24).
assert (HE25 : ew E 25 = Z_to_bv 64 mp) by (rewrite HE0, (TE_reg regs _ _ _ _ more 25%bv 25) by reflexivity; exact H25).
assert (HE26 : ew E 26 = Z_to_bv 64 c) by (rewrite HE0, (TE_reg regs _ _ _ _ more 26%bv 26) by reflexivity; exact H26).
assert (HE27 : ew E 27 = Z_to_bv 64 row) by (rewrite HE0, (TE_reg regs _ _ _ _ more 27%bv 27) by reflexivity; exact H27).
Local Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (tcx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app tcx_tabs fst snd zz_disj y_tisz y_tmsz y_cap cap] in Hs.
assert (HS : st_ok ubs0segs E ss_tsw2 (mkst regs (Z_to_bv 64 TPC_SW2) memc (seg_rom ubs0segs))).
{ unfold ss_tsw2, tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs (lp + 1) dp mp more memc TPC_SW2 true); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HFX.
- exact HGA.
- intros _ a Ha. apply (present_writable ubs0_msyms). replace a with (y_g cx + (a - y_g cx)) by lia. apply Pg. lia.
- lia.
- lia.
- lia.
- vm_compute; reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ apply (region_ok_regw _ E memc 45 2 (y_tm cx + 2 * (row + c)) HE45); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs0_msyms). apply Ptmc. exact Ho.
+ apply (region_ok_regw _ E memc 46 2 (y_lm cx + 2 * q) HE46); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs0_msyms). apply Plmc. exact Ho.
- cbn [all_disjoint app]; unfold extent_disjoint, regw, gen_region; cbn [r_base r_lo r_hi base_val app].
rewrite HE8, HE45, HE46, !unsigned_lit_small by lia.
split; [septac HSEP 4%nat 6%nat; lia|]. split; [septac HSEP 1%nat 6%nat; lia | exact I].
- cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, regw; cbn [r_base r_lo r_hi base_val].
rewrite HE45, HE46, !unsigned_lit_small by lia.
split; [split; [septac HSEP 1%nat 4%nat; lia | exact I]|]. split; exact I.
- unfold tsw_facts. cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE22, HE23, HE24, HE26, HE27, HE44, HE45, HE46, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r. repeat split; try lia.
+ apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists (row + c); lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3].
+ apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rlm3].
- unfold tsw_conds. cbn [conds_ok]. split; [|split; [|split; [|exact I]]].
+ apply (cond_geu E 45 0 36 0 (y_tm cx + 2 * (row + c)) (y_tm cx) HE45 HE36); lia.
+ apply (cond_geu E 46 0 33 0 (y_lm cx + 2 * q) (y_lm cx) HE46 HE33); lia.
+ apply cond_ne_U. rewrite (U_ptrchk0 E 45 36 (y_tm cx + 2 * (row + c)) (y_tm cx) HE45 HE36) by lia. rewrite U_lit by lia. lia.
- unfold tsw_alias. cbn [alias_ok]. split; [|split; [|split; [|exact I]]].
+ apply (alias_add E 27 26 44 row c HE27 HE26 HE44); lia.
+ apply (alias_b2i' E 36 44 45 (y_tm cx) (row + c) HE36 HE44 HE45); lia.
+ apply (alias_add E 33 23 46 (y_lm cx) (2 * q) HE33 HE23 HE46); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_SW2) memc (seg_rom ubs0segs))) in HJ.
pose proof (HWT (y_g cx, 72) ltac:(inl)) as Wg.
pose proof (HWT (y_tm cx, 4098 * y_idl cx) ltac:(cbv [tcx_tabs y_tmsz In]; unfold y_tmsz; inl')) as Wtm.
pose proof (HWT (y_lm cx, 8192) ltac:(inl)) as Wlm.
jrun_to LAWS ubs0tbl_ok HS HJ TPC_TAIL.
{ wr_norm.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 8); [reflexivity | rewrite HE8; apply unsigned_lit_small; lia | |].
{ cbn [r_wlo r_whi gen_region]. intros a Ha. eapply (wr_byte_of_wtok _ _ _ _ _ (y_g cx) 72); [exact Wg | apply HBt; inl | lia]. }
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 45); [reflexivity | rewrite HE45; apply unsigned_lit_small; lia | |].
{ cbn [r_wlo r_whi regw]. intros a Ha. eapply (wr_byte_of_wtok _ _ _ _ _ (y_tm cx) (4098 * y_idl cx)); [exact Wtm | apply HBt; cbv [tcx_tabs y_tmsz In]; unfold y_tmsz; inl' | lia]. }
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 46); [reflexivity | rewrite HE46; apply unsigned_lit_small; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi regw]. intros a Ha. eapply (wr_byte_of_wtok _ _ _ _ _ (y_lm cx) 8192); [exact Wlm | apply HBt; inl | lia]. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch type of HS with st_ok _ _ _ ?msx =>
exists (ms_regs msx), (ms_mem msx),
(mkLA TI (updn LM (Z.to_nat q) mp) LI (updn (zero_range TM (Z.to_nat row) (Z.to_nat (y_idl cx))) (Z.to_nat (row + c)) dp)
s1 (lp + 1) (dp + 1) (mp + 1) (Cn + 1) R) end.
split; [reflexivity|]. split; [exact HJ|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs (tcx_extra cx (lp + 1) dp mp ++ more) TREGS_FIXL HS
ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
lazymatch goal with HF1 : frame_of ?E1 ?rs ?m0 ?m' |- _ =>
assert (Hout : forall a, 0 <= a < 2 ^ 64 ->
outside [(y_g cx + 60, y_g cx + 68); (y_tm cx + 2 * (row + c), y_tm cx + 2 * (row + c) + 2); (y_lm cx + 2 * q, y_lm cx + 2 * q + 2)] a ->
mbyte ubs0segs m' a = mbyte ubs0segs m0 a)
by (intros a Ha Hws; eapply (tframe_mbyte_list E1 _ _ _ [(y_g cx + 60, y_g cx + 68); (y_tm cx + 2 * (row + c), y_tm cx + 2 * (row + c) + 2); (y_lm cx + 2 * q, y_lm cx + 2 * q + 2)] a HF1 Ha);
[ repeat (apply Forall2_cons; [first [left; cbn; lia | right; cbn [fst snd r_base r_wlo r_whi regw gen_region base_val]; rewrite ?HE8, ?HE45, ?HE46, ?unsigned_lit_small by lia; lia]|]); apply Forall2_nil
| exact Hws ]);
cbn [ms_mem] in Hout
end.
split; [intros a Ha; apply Hout; [lia | cbn -[Z.add Z.mul Z.sub]; repeat split; lia]|].
assert (Hgout : forall k, y_g cx <= k < y_g cx + 60 ->
outside [(y_g cx + 60, y_g cx + 68); (y_tm cx + 2 * (row + c), y_tm cx + 2 * (row + c) + 2); (y_lm cx + 2 * q, y_lm cx + 2 * q + 2)] k).
{ intros k Hk. cbn -[Z.add Z.mul Z.sub]. split; [lia|]. split; [septac HSEP 4%nat 6%nat; lia|]. split; [septac HSEP 1%nat 6%nat; lia|]. exact I. }
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (Vtm : val_mem ubs0segs (ms_mem msx) (y_tm cx + 2 * (row + c)) 2 dp);
[ rewrite <- (Z.add_0_r (y_tm cx + 2 * (row + c))); change 2%nat with (N.to_nat 2);
eapply (tval_mem_of_chunk E _ _ 45%nat); [eapply (tst_ok_region_nth _ _ _ 1 _ HS); reflexivity | reflexivity | inl
| rewrite HE45; apply unsigned_lit_small; lia | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE24, Z.add_0_r, unsigned_lit_small by lia; reflexivity |];
assert (Vlm : val_mem ubs0segs (ms_mem msx) (y_lm cx + 2 * q) 2 mp);
[ rewrite <- (Z.add_0_r (y_lm cx + 2 * q)); change 2%nat with (N.to_nat 2);
eapply (tval_mem_of_chunk E _ _ 46%nat); [eapply (tst_ok_region_nth _ _ _ 2 _ HS); reflexivity | reflexivity | inl
| rewrite HE46; apply unsigned_lit_small; lia | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE25, Z.add_0_r, unsigned_lit_small by lia; reflexivity |]
end.
replace (s1 - 1 + 1) with s1 in HIsw by lia.
unfold ttail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split; [| split; [reflexivity|]; split; [reflexivity|];
cbn [la_lp] in LenLD;
eapply (vtabs_keep_len memc _ cx PIX V1
(fun a => (y_g cx + 60 <= a < y_g cx + 68) \/ (y_tm cx + 2 * (row + c) <= a < y_tm cx + 2 * (row + c) + 2) \/ (y_lm cx + 2 * q <= a < y_lm cx + 2 * q + 2)) HVT LenLC LenPIX ltac:(lia));
[ intros a Ha Hna; apply Hout; [exact Ha | cbn -[Z.add Z.mul Z.sub]; repeat split; try lia; tauto]
| rewrite LenLD; split; [|split]; intros a Ha; (split; [lia|]); intros [Hw | [Hw | Hw]];
[ septac HSEP 2%nat 6%nat; lia | septac HSEP 2%nat 4%nat; lia | septac HSEP 1%nat 2%nat; lia
| septac HSEP 6%nat 7%nat; lia | septac HSEP 4%nat 7%nat; lia | septac HSEP 1%nat 7%nat; lia
| septac HSEP 5%nat 6%nat; lia | septac HSEP 4%nat 5%nat; lia | septac HSEP 1%nat 5%nat; lia ] ] ].
split; [apply (tlzw_regs_fix_kept regs); [exact HFX | intros r Hr; apply HK; exact Hr]|].
split.
{ pose proof (tst_ok_region_nth E _ _ 0 _ HS eq_refl) as HRg.
assert (G8 : bv_unsigned (ew E 8) = y_g cx) by (rewrite HE8; apply unsigned_lit_small; lia).
destruct HGA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V60 & _).
Local Ltac gfield V Hout Hgout := intros k Hk; rewrite Hout; [apply V; exact Hk | cbn in Hk; lia | apply Hgout; cbn in Hk; lia].
unfold gen_at. repeat split;
[ gfield V0 Hout Hgout | gfield V8 Hout Hgout | gfield V16 Hout Hgout | gfield V24 Hout Hgout
| gfield V32 Hout Hgout | gfield V40 Hout Hgout | gfield V48 Hout Hgout | gfield V56 Hout Hgout
| change 4%nat with (N.to_nat 4); eapply (tval_mem_of_chunk E _ _ 8%nat (y_g cx) 60 4); [exact HRg | reflexivity | inl | exact G8 | | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia];
cbn [sv_denot]; rewrite HE41, ?Z.add_0_r, unsigned_lit_small by lia; reflexivity
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E _ _ 8%nat (y_g cx) 64 2); [exact HRg | reflexivity | inl | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE42, unsigned_lit_small by lia; reflexivity
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E _ _ 8%nat (y_g cx) 66 2); [exact HRg | reflexivity | inl | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE43, unsigned_lit_small by lia; reflexivity ]. }
split.
{ split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- eapply arr16_frame; [exact ATI|]. intros a Ha. rewrite LenTI, Z2Nat.id in Ha by lia.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]. split; [septac HSEP 0%nat 6%nat; lia|]. split; [septac HSEP 0%nat 4%nat; lia|]. split; [septac HSEP 0%nat 1%nat; lia|]. exact I.
- eapply arr16_upd; [exact ALM | lia | exact HqLM | lia | exact Vlm |].
intros a Ha Hna. rewrite LenLM in Ha. cbn in Ha.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]. split; [septac HSEP 1%nat 6%nat; lia|]. split; [septac HSEP 1%nat 4%nat; lia|]. split; [lia|]. exact I.
- eapply arr16_frame; [exact ALI|]. intros a Ha. rewrite LenLI in Ha. cbn in Ha.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]. split; [septac HSEP 3%nat 6%nat; lia|]. split; [septac HSEP 3%nat 4%nat; lia|]. split; [septac HSEP 1%nat 3%nat; lia|]. exact I.
- eapply arr16_upd; [exact ATMz | lia | exact HJlen | lia | exact Vtm |].
intros a Ha Hna. rewrite LenTMz, Z2Nat.id in Ha by lia.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]. split; [septac HSEP 4%nat 6%nat; lia|]. split; [lia|]. split; [septac HSEP 1%nat 4%nat; lia|]. exact I. }
split; [exact HIsw|]. split; [treg_val HS (22%bv:reg)|]. lia.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
