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
YI00 YI02 YI01 YI07 YI03 YI04 YI06 YI5a YI0r UI2a UI2b UI2h.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac inl' := repeat (first [ left; reflexivity | right ]).
Ltac inl := cbv; inl'.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Local Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (tcx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app tcx_tabs fst snd zz_disj y_tisz y_tmsz y_cap cap] in Hs.
Local Ltac wr1 n HE W HBt untac :=
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ n); [reflexivity | rewrite HE; apply unsigned_lit_small; lia | |];
[ cbn [r_wlo r_whi gen_region regw reg16]; intros a Ha;
lazymatch type of W with wtok' _ _ _ _ (?d, ?n) => eapply (wr_byte_of_wtok _ _ _ _ _ d n); [exact W | apply HBt; untac; inl' | lia] end |].
Local Ltac wr_tac HE8 HE44 HE14 HE48 HE49 Wg Wld Wli Wlc Wtm HBt :=
wr_norm;
repeat first [ apply wr_ok_nil
| apply wr_ok_cons_ro; [zlit_tac|]
| wr1 8%nat HE8 Wg HBt ltac:(cbv)
| wr1 44%nat HE44 Wld HBt ltac:(cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap)
| wr1 14%nat HE14 Wli HBt ltac:(cbv)
| wr1 48%nat HE48 Wlc HBt ltac:(cbv)
| wr1 49%nat HE49 Wtm HBt ltac:(cbv [tcx_tabs y_tmsz In]; unfold y_tmsz) ].
Local Ltac gfield V Hout Hgout := intros k Hk; rewrite Hout; [apply V; exact Hk | cbn in Hk; lia | apply Hgout; cbn in Hk; lia].
Local Ltac gen_tac HS HE8 HE41 HE42 HE43 HGA Hout Hgout g :=
let HRg := fresh "HRg" in let G8 := fresh "G8" in
lazymatch type of HS with st_ok _ ?E1 _ _ =>
pose proof (tst_ok_region_nth E1 _ _ 0 _ HS eq_refl) as HRg;
assert (G8 : bv_unsigned (ew E1 8) = g) by (rewrite HE8; apply unsigned_lit_small; lia);
let V0 := fresh "V" in let V8 := fresh "V" in let V16 := fresh "V" in let V24 := fresh "V" in let V32 := fresh "V" in
let V40 := fresh "V" in let V48 := fresh "V" in let V56 := fresh "V" in
destruct HGA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & _);
unfold gen_at; repeat split;
[ gfield V0 Hout Hgout | gfield V8 Hout Hgout | gfield V16 Hout Hgout | gfield V24 Hout Hgout
| gfield V32 Hout Hgout | gfield V40 Hout Hgout | gfield V48 Hout Hgout | gfield V56 Hout Hgout
| change 4%nat with (N.to_nat 4); eapply (tval_mem_of_chunk E1 _ _ 8%nat g 60 4); [exact HRg | reflexivity | inl | exact G8 | | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia];
cbn [sv_denot]; rewrite HE41, unsigned_lit_small by lia; reflexivity
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E1 _ _ 8%nat g 64 2); [exact HRg | reflexivity | inl | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE42, ?Z.add_0_r, unsigned_lit_small by lia; reflexivity
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E1 _ _ 8%nat g 66 2); [exact HRg | reflexivity | inl | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE43, Z.add_0_r, unsigned_lit_small by lia; reflexivity ]
end.
Local Ltac mk_out HF1 ws HE8 HE44 HE14 HE48 HE49 :=
lazymatch type of HF1 with frame_of ?E1 ?rs ?m0 ?m' =>
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> outside ws a -> mbyte ubs2segs m' a = mbyte ubs2segs m0 a)
by (intros a Ha Hws; eapply (tframe_mbyte_list E1 _ _ _ ws a HF1 Ha);
[ repeat (apply Forall2_cons; [first [left; cbn; lia | right; cbn [fst snd r_base r_wlo r_whi regw reg16 tms_img1 gen_region base_val]; rewrite ?HE8, ?HE44, ?HE14, ?HE48, ?HE49, ?unsigned_lit_small by lia; lia]|]); apply Forall2_nil
| exact Hws ]);
cbn [ms_mem] in Hout
end.
Lemma tmiss_first : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c,
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X -> lzw_inv (y_idl cx) (y_nP cx) X ->
tmiss_pre cx regs s1 q ->
la_s X < s1 <= y_nP cx - 1 -> 0 <= q < 4096 -> 0 <= c < y_idl cx -> val_mem ubs2segs memc (y_img cx + s1) 1 c ->
la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 = 0 -> nth (Z.to_nat q) (la_LI X) 0 = 0 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs' mem' o,
c' = mkCfg (mkst regs' (Z_to_bv 64 (tmo_pc o)) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ tabove_eq cx memc mem' /\
tmo_post cx X s1 q c regs' mem' o).
Proof.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c
HCX HRG HSEP HBL HWIN HWT HJ HFX HGA HT HI (H22 & H10 & H17 & H14 & H12 & H23 & H13) Hs1 Hq Hc HC Hdplt HLM0 HLI0.
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
pose proof (mp_bound (y_idl cx) (y_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
destruct (LI_read (y_idl cx) (y_nP cx) _ q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI.
destruct (LM_read (y_idl cx) (y_nP cx) _ q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM.
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
destruct HT as (ATI & ALM & ALI & ATM).
destruct (arr16_nthZ ubs2segs memc (y_li cx) LI q ALI ltac:(lia) HqLI) as [VLI _].
destruct (arr16_nthZ ubs2segs memc (y_lm cx) LM q ALM ltac:(lia) HqLM) as [VLM _].
fold vLI in VLI. fold vLM in VLM.
assert (DvLI : vLI = nth (Z.to_nat q) LI 0) by reflexivity. assert (DvLM : vLM = nth (Z.to_nat q) LM 0) by reflexivity.
clearbody vLI vLM.
remember ((vLM - 1) * y_idl cx + c) as j eqn:Hj.
assert (Hrow : 0 <= (mp - 1) * y_idl cx <= 2046 * 256).
{ split; [apply Z.mul_nonneg_nonneg; lia | ]. apply (Z.le_trans _ (2046 * y_idl cx)); [apply Z.mul_le_mono_nonneg_r; lia | apply Z.mul_le_mono_nonneg_l; lia]. }
assert (Hrow2 : 2 * ((mp - 1) * y_idl cx) + 2 * y_idl cx <= 4098 * y_idl cx).
{ assert (mp * y_idl cx <= 2047 * y_idl cx) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
assert (Pld : forall i, 0 <= i < 2 -> present memc (y_ld cx + 2 * lp + i)).
{ intros i Hi. replace (y_ld cx + 2 * lp + i) with (y_ld cx + (2 * lp + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx)) (2 * lp + i) HH ltac:(apply HBt; inl) ltac:(lia))). }
assert (Pg : forall i, 0 <= i < 72 -> present memc (y_g cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_g cx) 72 i HH ltac:(apply HBt; inl) Hi)). }
assert (Plc : forall i, 0 <= i < 1 -> present memc (y_lc cx + q + i)).
{ intros i Hi. replace (y_lc cx + q + i) with (y_lc cx + (q + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_lc cx) 4096 (q + i) HH ltac:(apply HBt; inl) ltac:(lia))). }
assert (Ptm : forall i, 0 <= i < 4098 * y_idl cx -> present memc (y_tm cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_tm cx) (4098 * y_idl cx) i HH ltac:(apply HBt; inl) Hi)). }
remember [Z_to_bv 64 (y_ld cx + 2 * lp); Z_to_bv 64 c; Z_to_bv 64 vLM; Z_to_bv 64 vLI; Z_to_bv 64 (y_lc cx + q);
Z_to_bv 64 (y_tm cx + 2 * j); Z_to_bv 64 (y_tm cx + 2 * ((mp - 1) * y_idl cx))] as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
assert (HE44 : ew E 44 = Z_to_bv 64 (y_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 44), (TE_more regs _ _ _ _ more 0), Hmore; reflexivity).
assert (HE45 : ew E 45 = Z_to_bv 64 c) by (rewrite HE0; change 45%nat with (44 + 1)%nat; rewrite (TE_more regs _ _ _ _ more 1), Hmore; reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 vLM) by (rewrite HE0; change 46%nat with (44 + 2)%nat; rewrite (TE_more regs _ _ _ _ more 2), Hmore; reflexivity).
assert (HE47 : ew E 47 = Z_to_bv 64 vLI) by (rewrite HE0; change 47%nat with (44 + 3)%nat; rewrite (TE_more regs _ _ _ _ more 3), Hmore; reflexivity).
assert (HE48 : ew E 48 = Z_to_bv 64 (y_lc cx + q)) by (rewrite HE0; change 48%nat with (44 + 4)%nat; rewrite (TE_more regs _ _ _ _ more 4), Hmore; reflexivity).
assert (HE49 : ew E 49 = Z_to_bv 64 (y_tm cx + 2 * j)) by (rewrite HE0; change 49%nat with (44 + 5)%nat; rewrite (TE_more regs _ _ _ _ more 5), Hmore; reflexivity).
assert (HE50 : ew E 50 = Z_to_bv 64 (y_tm cx + 2 * ((mp - 1) * y_idl cx))) by (rewrite HE0; change 50%nat with (44 + 6)%nat; rewrite (TE_more regs _ _ _ _ more 6), Hmore; reflexivity).
pose proof (TE_sp regs cx lp dp mp more HFX) as HE2. pose proof (TE_g regs cx lp dp mp more HFX) as HE8.
pose proof (TE_idl regs cx lp dp mp more HFX) as HE20. pose proof (TE_idl2 regs cx lp dp mp more HFX) as HE21.
pose proof (TE_ti regs cx lp dp mp more) as HE32. pose proof (TE_lm regs cx lp dp mp more) as HE33.
pose proof (TE_lc regs cx lp dp mp more) as HE34. pose proof (TE_li regs cx lp dp mp more) as HE35.
pose proof (TE_tm regs cx lp dp mp more) as HE36. pose proof (TE_ld regs cx lp dp mp more) as HE37.
pose proof (TE_img regs cx lp dp mp more) as HE38. pose proof (TE_nP regs cx lp dp mp more) as HE39.
pose proof (TE_lp regs cx lp dp mp more) as HE41. pose proof (TE_dp regs cx lp dp mp more) as HE42. pose proof (TE_mp regs cx lp dp mp more) as HE43.
rewrite <- HE0 in HE2, HE8, HE20, HE21, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE41, HE42, HE43.
assert (HE22 : ew E 22 = Z_to_bv 64 s1) by (rewrite HE0, (TE_reg regs _ _ _ _ more 22%bv 22) by reflexivity; exact H22).
assert (HE10 : ew E 10 = Z_to_bv 64 q) by (rewrite HE0, (TE_reg regs _ _ _ _ more 10%bv 10) by reflexivity; exact H10).
assert (HE17 : ew E 17 = Z_to_bv 64 (y_lm cx + 2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 17%bv 17) by reflexivity; exact H17).
assert (HE14 : ew E 14 = Z_to_bv 64 (y_li cx + 2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 14%bv 14) by reflexivity; exact H14).
assert (HE12 : ew E 12 = Z_to_bv 64 (y_img cx + s1)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 12%bv 12) by reflexivity; exact H12).
assert (HE23 : ew E 23 = Z_to_bv 64 (2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 23%bv 23) by reflexivity; exact H23).
assert (HE13 : ew E 13 = Z_to_bv 64 q) by (rewrite HE0, (TE_reg regs _ _ _ _ more 13%bv 13) by reflexivity; exact H13).
assert (FACTS0 : atoms_ok E (tms_facts false)).
{ unfold tms_facts. rewrite app_nil_r. cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE10, HE12, HE13, HE14, HE17, HE22, HE23, HE44, HE45, HE46, HE47, HE48, HE50, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r. repeat split; try lia.
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rli3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rlm3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists ((mp - 1) * y_idl cx); lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3]. }
assert (HUROW : U E tms_ROW = (mp - 1) * y_idl cx) by (unfold tms_ROW; apply (U_mulw_row E 43 20 mp (y_idl cx) HE43 HE20); lia).
assert (ALIAS0 : alias_ok E (tms_alias false)).
{ unfold tms_alias. rewrite app_nil_r. cbn [alias_ok]. split; [|split; [|split; [|split; [|exact I]]]].
- apply (alias_b2i' E 37 41 44 (y_ld cx) lp HE37 HE41 HE44); lia.
- apply (alias_add E 34 13 48 (y_lc cx) q HE34 HE13 HE48); lia.
- apply (alias_add E 35 23 14 (y_li cx) (2 * q) HE35 HE23 HE14); lia.
- apply (alias_sll1_base E 36 50 tms_ROW (y_tm cx) ((mp - 1) * y_idl cx) HE36 HUROW HE50); lia. }
assert (CONDLD : acond_ok E (mkAC BC_GEU (SOff 44%nat 0) (SOff 37%nat 0))) by (apply (cond_geu E 44 0 37 0 (y_ld cx + 2 * lp) (y_ld cx) HE44 HE37); lia).
assert (RLD : region_ok ubs2segs E memc (regw 44 2)).
{ apply (region_ok_regw _ E memc 44 2 (y_ld cx + 2 * lp) HE44); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs2_msyms). apply Pld. exact Ho. }
assert (RIMG : region_ok ubs2segs E memc tms_img1).
{ unfold region_ok, tms_img1. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE12, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE45, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (RLM : region_ok ubs2segs E memc (reg16 17 46 false)).
{ eapply (region_ok_reg16 _ E memc 17 46 false (y_lm cx + 2 * q) vLM HE17 HE46); [lia | lia | lia | exact VLM | intros X0; discriminate X0]. }
pose proof (HWT (y_g cx, 72) ltac:(inl)) as Wg.
pose proof (HWT (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) ltac:(cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; inl')) as Wld.
pose proof (HWT (y_tm cx, 4098 * y_idl cx) ltac:(cbv [tcx_tabs y_tmsz In]; unfold y_tmsz; inl')) as Wtm.
pose proof (HWT (y_li cx, 8192) ltac:(inl)) as Wli.
pose proof (HWT (y_lc cx, 4096) ltac:(inl)) as Wlc.
assert (Pli : forall i, 0 <= i < 2 -> present memc (y_li cx + 2 * q + i)).
{ intros i Hi. replace (y_li cx + 2 * q + i) with (y_li cx + (2 * q + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_li cx) 8192 (2 * q + i) HH ltac:(apply HBt; inl) ltac:(lia))). }
assert (HS : st_ok ubs2segs E ss_tms_first (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs2segs))).
{ unfold ss_tms_first, tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more memc TPC_MISS true); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HFX.
- exact HGA.
- intros _ a Ha. apply (present_writable ubs2_msyms). replace a with (y_g cx + (a - y_g cx)) by lia. apply Pg. lia.
- lia.
- lia.
- lia.
- vm_compute; reflexivity.
- apply Forall_cons; [exact RLD|]. apply Forall_cons; [exact RIMG|]. apply Forall_cons; [exact RLM|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ eapply (region_ok_reg16 _ E memc 14 47 true (y_li cx + 2 * q) vLI HE14 HE47); [lia | lia | lia | exact VLI |].
intros _ o Ho. apply (present_writable ubs2_msyms). apply Pli. exact Ho.
+ apply (region_ok_regw _ E memc 48 1 (y_lc cx + q) HE48); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs2_msyms). apply Plc. exact Ho.
- unfold tms_regions_first. cbn [all_disjoint app]; unfold extent_disjoint, regw, reg16, tms_img1, gen_region; cbn [r_base r_lo r_hi base_val app].
rewrite HE8, HE44, HE12, HE17, HE14, HE48, !unsigned_lit_small by lia.
split; [septac HSEP 5%nat 6%nat; lia|]. split; [septac HSEP 6%nat 7%nat; lia|]. split; [septac HSEP 1%nat 6%nat; lia|].
split; [septac HSEP 3%nat 6%nat; lia|]. split; [septac HSEP 2%nat 6%nat; lia | exact I].
- unfold tms_regions_first. cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, regw, reg16, tms_img1; cbn [r_base r_lo r_hi base_val].
rewrite HE44, HE12, HE17, HE14, HE48, !unsigned_lit_small by lia.
split; [split; [septac HSEP 5%nat 7%nat; lia | split; [septac HSEP 1%nat 5%nat; lia | split; [septac HSEP 3%nat 5%nat; lia | split; [septac HSEP 2%nat 5%nat; lia | exact I]]]]|].
split; [split; [septac HSEP 1%nat 7%nat; lia | split; [septac HSEP 3%nat 7%nat; lia | split; [septac HSEP 2%nat 7%nat; lia | exact I]]]|].
split; [split; [septac HSEP 1%nat 3%nat; lia | split; [septac HSEP 1%nat 2%nat; lia | exact I]]|].
split; [split; [septac HSEP 2%nat 3%nat; lia | exact I]|]. split; exact I.
- exact FACTS0.
- unfold tms_conds_first. cbn [conds_ok]. split; [exact CONDLD|]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
+ apply cond_eq_U. rewrite (U_dpfull12 E 42 dp HE42), U_SLit by lia. rewrite (proj2 (Z.eqb_neq dp 4096) ltac:(lia)). reflexivity.
+ apply (cond_eq_lit E 46 vLM 0 HE46); lia.
+ apply (cond_eq_lit E 47 vLI 0 HE47); lia.
+ apply (cond_geu E 48 0 34 0 (y_lc cx + q) (y_lc cx) HE48 HE34); lia.
+ apply (cond_geu E 14 0 35 0 (y_li cx + 2 * q) (y_li cx) HE14 HE35); lia.
- exact ALIAS0. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs2segs))) in HJ.
clear Ptm.
jrun_to LAWS ubs2tbl_ok HS HJ TPC_TAIL; [wr_tac HE8 HE44 HE14 HE48 HE49 Wg Wld Wli Wlc Wtm HBt|].
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch type of HS with st_ok _ _ _ ?msx =>
exists (ms_regs msx), (ms_mem msx), (TMO_tail (mkLA TI LM (updn LI (Z.to_nat q) dp) TM s1 (lp + 1) (dp + 1) mp (Cn + 1) R)) end.
split; [reflexivity|]. split; [exact HJ|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs (tcx_extra cx lp dp mp ++ more) TREGS_FIXL HS
ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
lazymatch goal with HF1 : frame_of _ _ _ _ |- _ =>
mk_out HF1 [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2); (0, 0); (0, 0); (y_li cx + 2 * q, y_li cx + 2 * q + 2); (y_lc cx + q, y_lc cx + q + 1)] HE8 HE44 HE14 HE48 HE49 end.
split; [intros a Ha; apply Hout; [lia | cbn -[Z.add Z.mul Z.sub]; repeat split; lia]|].
assert (Hgout : forall k, y_g cx <= k < y_g cx + 60 ->
outside [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2); (0, 0); (0, 0); (y_li cx + 2 * q, y_li cx + 2 * q + 2); (y_lc cx + q, y_lc cx + q + 1)] k).
{ intros k Hk. cbn -[Z.add Z.mul Z.sub]; split; [lia|]; split; [septac HSEP 5%nat 6%nat; lia|]; split; [lia|]; split; [lia|]; split; [septac HSEP 3%nat 6%nat; lia|]; split; [septac HSEP 2%nat 6%nat; lia|]; exact I. }
assert (Vnew : val_mem ubs2segs ltac:(lazymatch type of HS with st_ok _ _ _ ?msx => exact (ms_mem msx) end) (y_li cx + 2 * q) 2 dp).
{ rewrite <- (Z.add_0_r (y_li cx + 2 * q)). change 2%nat with (N.to_nat 2).
eapply (tval_mem_of_chunk E _ _ 14%nat); [eapply (tst_ok_region_nth _ _ _ 4 _ HS); reflexivity | reflexivity | inl
| rewrite HE14; apply unsigned_lit_small; lia | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia].
cbn [sv_denot]. rewrite HE42, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (HT' : ttables_at ltac:(lazymatch type of HS with st_ok _ _ _ ?msx => exact (ms_mem msx) end) cx
(mkLA TI LM (updn LI (Z.to_nat q) dp) TM s1 (lp + 1) (dp + 1) mp (Cn + 1) R)).
{ split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- eapply arr16_frame; [exact ATI|]. intros a Ha. rewrite LenTI, Z2Nat.id in Ha by lia.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 0%nat 6%nat; lia|]; split; [septac HSEP 0%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [septac HSEP 0%nat 3%nat; lia|]; split; [septac HSEP 0%nat 2%nat; lia|]; exact I.
- eapply arr16_frame; [exact ALM|]. intros a Ha. rewrite LenLM in Ha. cbn in Ha.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 1%nat 6%nat; lia|]; split; [septac HSEP 1%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [septac HSEP 1%nat 3%nat; lia|]; split; [septac HSEP 1%nat 2%nat; lia|]; exact I.
- eapply arr16_upd; [exact ALI | lia | exact HqLI | lia | exact Vnew |].
intros a Ha Hna. rewrite LenLI in Ha. cbn in Ha.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 3%nat 6%nat; lia|]; split; [septac HSEP 3%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [septac HSEP 2%nat 3%nat; lia|]; exact I.
- eapply arr16_frame; [exact ATM|]. intros a Ha. rewrite LenTM, Z2Nat.id in Ha by lia.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 4%nat 6%nat; lia|]; split; [septac HSEP 4%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [septac HSEP 3%nat 4%nat; lia|]; split; [septac HSEP 2%nat 4%nat; lia|]; exact I. }
pose proof (inv_first (y_idl cx) (y_nP cx) Hidl _ q (s1 - 1) HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) Hq) as HI'.
cbn [st_first la_LI la_LM] in HI'. specialize (HI' ltac:(rewrite <- DvLI; exact HLI0) ltac:(rewrite <- DvLM; exact HLM0)).
replace (s1 - 1 + 1) with s1 in HI' by lia.
unfold tmo_post, ttail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split; [|reflexivity].
split; [apply (tlzw_regs_fix_kept regs); [exact HFX | intros r Hr; apply HK; exact Hr]|].
split; [gen_tac HS HE8 HE41 HE42 HE43 HGA Hout Hgout (y_g cx)|].
split; [exact HT'|]. split; [exact HI'|]. split; [treg_val HS (22%bv:reg) | lia].
Qed.
Lemma tmiss_sw : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c,
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X -> lzw_inv (y_idl cx) (y_nP cx) X ->
tmiss_pre cx regs s1 q ->
la_s X < s1 <= y_nP cx - 1 -> 0 <= q < 4096 -> 0 <= c < y_idl cx -> val_mem ubs2segs memc (y_img cx + s1) 1 c ->
la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 = 0 -> nth (Z.to_nat q) (la_LI X) 0 <> 0 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs' mem' o,
c' = mkCfg (mkst regs' (Z_to_bv 64 (tmo_pc o)) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ tabove_eq cx memc mem' /\
tmo_post cx X s1 q c regs' mem' o).
Proof.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c
HCX HRG HSEP HBL HWIN HWT HJ HFX HGA HT HI (H22 & H10 & H17 & H14 & H12 & H23 & H13) Hs1 Hq Hc HC Hdplt HLM0 HLI1.
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
pose proof (mp_bound (y_idl cx) (y_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
destruct (LI_read (y_idl cx) (y_nP cx) _ q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI.
destruct (LM_read (y_idl cx) (y_nP cx) _ q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM.
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
destruct HT as (ATI & ALM & ALI & ATM).
destruct (arr16_nthZ ubs2segs memc (y_li cx) LI q ALI ltac:(lia) HqLI) as [VLI _].
destruct (arr16_nthZ ubs2segs memc (y_lm cx) LM q ALM ltac:(lia) HqLM) as [VLM _].
fold vLI in VLI. fold vLM in VLM.
assert (DvLI : vLI = nth (Z.to_nat q) LI 0) by reflexivity. assert (DvLM : vLM = nth (Z.to_nat q) LM 0) by reflexivity.
clearbody vLI vLM.
remember ((vLM - 1) * y_idl cx + c) as j eqn:Hj.
assert (Hrow : 0 <= (mp - 1) * y_idl cx <= 2046 * 256).
{ split; [apply Z.mul_nonneg_nonneg; lia | ]. apply (Z.le_trans _ (2046 * y_idl cx)); [apply Z.mul_le_mono_nonneg_r; lia | apply Z.mul_le_mono_nonneg_l; lia]. }
assert (Hrow2 : 2 * ((mp - 1) * y_idl cx) + 2 * y_idl cx <= 4098 * y_idl cx).
{ assert (mp * y_idl cx <= 2047 * y_idl cx) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
assert (Pld : forall i, 0 <= i < 2 -> present memc (y_ld cx + 2 * lp + i)).
{ intros i Hi. replace (y_ld cx + 2 * lp + i) with (y_ld cx + (2 * lp + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx)) (2 * lp + i) HH ltac:(apply HBt; inl) ltac:(lia))). }
assert (Pg : forall i, 0 <= i < 72 -> present memc (y_g cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_g cx) 72 i HH ltac:(apply HBt; inl) Hi)). }
assert (Plc : forall i, 0 <= i < 1 -> present memc (y_lc cx + q + i)).
{ intros i Hi. replace (y_lc cx + q + i) with (y_lc cx + (q + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_lc cx) 4096 (q + i) HH ltac:(apply HBt; inl) ltac:(lia))). }
assert (Ptm : forall i, 0 <= i < 4098 * y_idl cx -> present memc (y_tm cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_tm cx) (4098 * y_idl cx) i HH ltac:(apply HBt; inl) Hi)). }
remember [Z_to_bv 64 (y_ld cx + 2 * lp); Z_to_bv 64 c; Z_to_bv 64 vLM; Z_to_bv 64 vLI; Z_to_bv 64 (y_lc cx + q);
Z_to_bv 64 (y_tm cx + 2 * j); Z_to_bv 64 (y_tm cx + 2 * ((mp - 1) * y_idl cx))] as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
assert (HE44 : ew E 44 = Z_to_bv 64 (y_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 44), (TE_more regs _ _ _ _ more 0), Hmore; reflexivity).
assert (HE45 : ew E 45 = Z_to_bv 64 c) by (rewrite HE0; change 45%nat with (44 + 1)%nat; rewrite (TE_more regs _ _ _ _ more 1), Hmore; reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 vLM) by (rewrite HE0; change 46%nat with (44 + 2)%nat; rewrite (TE_more regs _ _ _ _ more 2), Hmore; reflexivity).
assert (HE47 : ew E 47 = Z_to_bv 64 vLI) by (rewrite HE0; change 47%nat with (44 + 3)%nat; rewrite (TE_more regs _ _ _ _ more 3), Hmore; reflexivity).
assert (HE48 : ew E 48 = Z_to_bv 64 (y_lc cx + q)) by (rewrite HE0; change 48%nat with (44 + 4)%nat; rewrite (TE_more regs _ _ _ _ more 4), Hmore; reflexivity).
assert (HE49 : ew E 49 = Z_to_bv 64 (y_tm cx + 2 * j)) by (rewrite HE0; change 49%nat with (44 + 5)%nat; rewrite (TE_more regs _ _ _ _ more 5), Hmore; reflexivity).
assert (HE50 : ew E 50 = Z_to_bv 64 (y_tm cx + 2 * ((mp - 1) * y_idl cx))) by (rewrite HE0; change 50%nat with (44 + 6)%nat; rewrite (TE_more regs _ _ _ _ more 6), Hmore; reflexivity).
pose proof (TE_sp regs cx lp dp mp more HFX) as HE2. pose proof (TE_g regs cx lp dp mp more HFX) as HE8.
pose proof (TE_idl regs cx lp dp mp more HFX) as HE20. pose proof (TE_idl2 regs cx lp dp mp more HFX) as HE21.
pose proof (TE_ti regs cx lp dp mp more) as HE32. pose proof (TE_lm regs cx lp dp mp more) as HE33.
pose proof (TE_lc regs cx lp dp mp more) as HE34. pose proof (TE_li regs cx lp dp mp more) as HE35.
pose proof (TE_tm regs cx lp dp mp more) as HE36. pose proof (TE_ld regs cx lp dp mp more) as HE37.
pose proof (TE_img regs cx lp dp mp more) as HE38. pose proof (TE_nP regs cx lp dp mp more) as HE39.
pose proof (TE_lp regs cx lp dp mp more) as HE41. pose proof (TE_dp regs cx lp dp mp more) as HE42. pose proof (TE_mp regs cx lp dp mp more) as HE43.
rewrite <- HE0 in HE2, HE8, HE20, HE21, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE41, HE42, HE43.
assert (HE22 : ew E 22 = Z_to_bv 64 s1) by (rewrite HE0, (TE_reg regs _ _ _ _ more 22%bv 22) by reflexivity; exact H22).
assert (HE10 : ew E 10 = Z_to_bv 64 q) by (rewrite HE0, (TE_reg regs _ _ _ _ more 10%bv 10) by reflexivity; exact H10).
assert (HE17 : ew E 17 = Z_to_bv 64 (y_lm cx + 2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 17%bv 17) by reflexivity; exact H17).
assert (HE14 : ew E 14 = Z_to_bv 64 (y_li cx + 2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 14%bv 14) by reflexivity; exact H14).
assert (HE12 : ew E 12 = Z_to_bv 64 (y_img cx + s1)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 12%bv 12) by reflexivity; exact H12).
assert (HE23 : ew E 23 = Z_to_bv 64 (2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 23%bv 23) by reflexivity; exact H23).
assert (HE13 : ew E 13 = Z_to_bv 64 q) by (rewrite HE0, (TE_reg regs _ _ _ _ more 13%bv 13) by reflexivity; exact H13).
assert (FACTS0 : atoms_ok E (tms_facts false)).
{ unfold tms_facts. rewrite app_nil_r. cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE10, HE12, HE13, HE14, HE17, HE22, HE23, HE44, HE45, HE46, HE47, HE48, HE50, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r. repeat split; try lia.
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rli3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rlm3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists ((mp - 1) * y_idl cx); lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3]. }
assert (HUROW : U E tms_ROW = (mp - 1) * y_idl cx) by (unfold tms_ROW; apply (U_mulw_row E 43 20 mp (y_idl cx) HE43 HE20); lia).
assert (ALIAS0 : alias_ok E (tms_alias false)).
{ unfold tms_alias. rewrite app_nil_r. cbn [alias_ok]. split; [|split; [|split; [|split; [|exact I]]]].
- apply (alias_b2i' E 37 41 44 (y_ld cx) lp HE37 HE41 HE44); lia.
- apply (alias_add E 34 13 48 (y_lc cx) q HE34 HE13 HE48); lia.
- apply (alias_add E 35 23 14 (y_li cx) (2 * q) HE35 HE23 HE14); lia.
- apply (alias_sll1_base E 36 50 tms_ROW (y_tm cx) ((mp - 1) * y_idl cx) HE36 HUROW HE50); lia. }
assert (CONDLD : acond_ok E (mkAC BC_GEU (SOff 44%nat 0) (SOff 37%nat 0))) by (apply (cond_geu E 44 0 37 0 (y_ld cx + 2 * lp) (y_ld cx) HE44 HE37); lia).
assert (RLD : region_ok ubs2segs E memc (regw 44 2)).
{ apply (region_ok_regw _ E memc 44 2 (y_ld cx + 2 * lp) HE44); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs2_msyms). apply Pld. exact Ho. }
assert (RIMG : region_ok ubs2segs E memc tms_img1).
{ unfold region_ok, tms_img1. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE12, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE45, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (RLM : region_ok ubs2segs E memc (reg16 17 46 false)).
{ eapply (region_ok_reg16 _ E memc 17 46 false (y_lm cx + 2 * q) vLM HE17 HE46); [lia | lia | lia | exact VLM | intros X0; discriminate X0]. }
pose proof (HWT (y_g cx, 72) ltac:(inl)) as Wg.
pose proof (HWT (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) ltac:(cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; inl')) as Wld.
pose proof (HWT (y_tm cx, 4098 * y_idl cx) ltac:(cbv [tcx_tabs y_tmsz In]; unfold y_tmsz; inl')) as Wtm.
pose proof (HWT (y_li cx, 8192) ltac:(inl)) as Wli.
pose proof (HWT (y_lc cx, 4096) ltac:(inl)) as Wlc.
assert (Prw : forall i, 0 <= i < 2 * y_idl cx -> present memc (y_tm cx + 2 * ((mp - 1) * y_idl cx) + i)).
{ intros i Hi. replace (y_tm cx + 2 * ((mp - 1) * y_idl cx) + i) with (y_tm cx + (2 * ((mp - 1) * y_idl cx) + i)) by lia. apply Ptm. lia. }
assert (HS : st_ok ubs2segs E ss_tms_sw (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs2segs))).
{ unfold ss_tms_sw, tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more memc TPC_MISS true); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HFX.
- exact HGA.
- intros _ a Ha. apply (present_writable ubs2_msyms). replace a with (y_g cx + (a - y_g cx)) by lia. apply Pg. lia.
- lia.
- lia.
- lia.
- vm_compute; reflexivity.
- apply Forall_cons; [exact RLD|]. apply Forall_cons; [exact RIMG|]. apply Forall_cons; [exact RLM|]. apply Forall_cons; [|apply Forall_nil].
eapply (region_ok_reg16 _ E memc 14 47 false (y_li cx + 2 * q) vLI HE14 HE47); [lia | lia | lia | exact VLI | intros X0; discriminate X0].
- unfold tms_regions_sw. cbn [all_disjoint app]; unfold extent_disjoint, regw, reg16, tms_img1, gen_region; cbn [r_base r_lo r_hi base_val app].
rewrite HE8, HE44, HE12, HE17, HE14, !unsigned_lit_small by lia.
split; [septac HSEP 5%nat 6%nat; lia|]. split; [septac HSEP 6%nat 7%nat; lia|]. split; [septac HSEP 1%nat 6%nat; lia|].
split; [septac HSEP 3%nat 6%nat; lia | exact I].
- unfold tms_regions_sw. cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, regw, reg16, tms_img1; cbn [r_base r_lo r_hi base_val].
rewrite HE44, HE12, HE17, HE14, !unsigned_lit_small by lia.
split; [split; [septac HSEP 5%nat 7%nat; lia | split; [septac HSEP 1%nat 5%nat; lia | split; [septac HSEP 3%nat 5%nat; lia | exact I]]]|].
split; [split; [septac HSEP 1%nat 7%nat; lia | split; [septac HSEP 3%nat 7%nat; lia | exact I]]|].
split; [split; [septac HSEP 1%nat 3%nat; lia | exact I]|]. split; exact I.
- exact FACTS0.
- unfold tms_conds_sw. cbn [conds_ok]. split; [exact CONDLD|]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
+ apply cond_eq_U. rewrite (U_dpfull12 E 42 dp HE42), U_SLit by lia. rewrite (proj2 (Z.eqb_neq dp 4096) ltac:(lia)). reflexivity.
+ apply (cond_eq_lit E 46 vLM 0 HE46); lia.
+ apply (cond_ne_lit E 47 vLI 0 HE47); lia.
+ apply cond_eq_U. rewrite HUROW, (U_mul_row64 E 43 20 mp (y_idl cx) HE43 HE20) by lia. reflexivity.
+ apply (cond_geu E 50 0 36 0 (y_tm cx + 2 * ((mp - 1) * y_idl cx)) (y_tm cx) HE50 HE36); lia.
+ apply cond_ne_U. rewrite (U_ptrchk E 50 36 tms_ROW (y_tm cx + 2 * ((mp - 1) * y_idl cx)) (y_tm cx) ((mp - 1) * y_idl cx) HE50 HE36 HUROW) by lia.
rewrite U_lit by lia. lia.
- exact ALIAS0. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memset; [wr_tac HE8 HE44 HE14 HE48 HE49 Wg Wld Wli Wlc Wtm HBt|].
lazymatch goal with HF1 : frame_of _ _ _ _ |- _ =>
mk_out HF1 [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2); (0, 0); (0, 0); (0, 0)] HE8 HE44 HE14 HE48 HE49 end.
rename Hout into Hout1.
assert (Hgout : forall k, y_g cx <= k < y_g cx + 60 ->
outside [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2); (0, 0); (0, 0); (0, 0)] k).
{ intros k Hk. cbn -[Z.add Z.mul Z.sub]; split; [lia|]; split; [septac HSEP 5%nat 6%nat; lia|]; split; [lia|]; split; [lia|]; split; [lia|]; exact I. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs (tcx_extra cx lp dp mp ++ more) (TREGS_FIXL ++ [22; 23]%bv) HS
ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (Ha0 : getr (ms_regs msx) 10 = Z_to_bv 64 (y_tm cx + 2 * ((mp - 1) * y_idl cx))) by (treg_val HS (10%bv:reg));
assert (Ha1 : getr (ms_regs msx) 11 = Z_to_bv 64 0) by (treg_val HS (11%bv:reg));
assert (Ha2 : getr (ms_regs msx) 12 = Z_to_bv 64 (2 * y_idl cx)) by (treg_val HS (12%bv:reg));
assert (Hra : getr (ms_regs msx) 1 = Z_to_bv 64 TPC_SW2) by (treg_val HS (1%bv:reg));
assert (Q24 : getr (ms_regs msx) 24 = Z_to_bv 64 dp) by (treg_val HS (24%bv:reg));
assert (Q26 : getr (ms_regs msx) 26 = Z_to_bv 64 c) by (treg_val HS (26%bv:reg));
assert (Q25 : getr (ms_regs msx) 25 = Z_to_bv 64 mp) by (treg_val HS (25%bv:reg));
assert (Q27 : getr (ms_regs msx) 27 = Z_to_bv 64 ((mp - 1) * y_idl cx))
by (let H := fresh "Hrv" in pose proof (st_ok_reg ubs2segs E _ _ (27%bv:reg) HS) as H; eval_sr_get_in H; rewrite H;
apply (denot_mulw_row E 43 20 mp (y_idl cx) HE43 HE20); lia);
assert (HGA1 : gen_at (ms_mem msx) cx (lp + 1) dp mp) by (gen_tac HS HE8 HE41 HE42 HE43 HGA Hout1 Hgout (y_g cx))
end.
eapply SR_mono.
{ eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset_spec
E _ _ STK sp0 FP L A mem md Lc Ac mdc (y_tm cx + 2 * ((mp - 1) * y_idl cx)) 0 (2 * y_idl cx));
[exact HS | reflexivity | reflexivity | exact HJ | exact Ha0 | exact Ha1 | exact Ha2 | exact Hra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | |].
- intros i Hi. lazymatch goal with HG1 : mem_grows _ _ |- _ => eapply (present_grows _ _ _ HG1) end. apply Prw. exact Hi.
- intros a Ha. eapply (wr_byte_of_wtok _ _ _ _ _ (y_tm cx) (4098 * y_idl cx)); [exact Wtm | apply HBt; cbv [tcx_tabs y_tmsz In]; unfold y_tmsz; inl' | lia]. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hr10 & Hkeep & Hout2 & Hgr2 & Hzero).
exists regs2, mem2, TMO_sw2. split; [reflexivity|]. split; [exact HJ2|].
assert (Hout : forall a, 0 <= a < 2 ^ 64 ->
outside [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2); (0, 0); (0, 0); (0, 0)] a ->
~ (y_tm cx + 2 * ((mp - 1) * y_idl cx) <= a < y_tm cx + 2 * ((mp - 1) * y_idl cx) + 2 * y_idl cx) ->
mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha Hws Hn3. etransitivity; [| apply (Hout1 a Ha Hws)]. apply tmbyte_eq_of1. apply Hout2. rewrite unsigned_lit_small by lia. lia. }
split; [intros a' Ha'; apply Hout; [lia | cbn -[Z.add Z.mul Z.sub]; repeat split; lia | lia]|].
unfold tmo_post, tsw2_pre. cbn [la_TI la_LM la_LI la_TM].
split. { apply (tlzw_regs_fix_kept regs); [exact HFX|]. intros r Hr. rewrite Hkeep by (apply tregs_fixl_not_memset; exact Hr).
apply HK. apply in_app_iff. left. exact Hr. }
split. { eapply gen_at_frame; [exact HGA1|]. intros a Ha. apply tmbyte_eq_of1. apply Hout2. rewrite unsigned_lit_small by lia.
septac HSEP 4%nat 6%nat. lia. }
split. { split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- eapply arr16_frame; [exact ATI|]. intros a Ha. rewrite LenTI, Z2Nat.id in Ha by lia.
apply Hout; [lia | cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 0%nat 6%nat; lia|]; split; [septac HSEP 0%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [lia|]; exact I | septac HSEP 0%nat 4%nat; lia].
- eapply arr16_frame; [exact ALM|]. intros a Ha. rewrite LenLM in Ha. cbn in Ha.
apply Hout; [lia | cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 1%nat 6%nat; lia|]; split; [septac HSEP 1%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [lia|]; exact I | septac HSEP 1%nat 4%nat; lia].
- eapply arr16_frame; [exact ALI|]. intros a Ha. rewrite LenLI in Ha. cbn in Ha.
apply Hout; [lia | cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 3%nat 6%nat; lia|]; split; [septac HSEP 3%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [lia|]; exact I | septac HSEP 3%nat 4%nat; lia].
- eapply arr16_zero_range; [exact ATM | lia | lia | rewrite LenTM; rewrite <- Z2Nat.inj_add by lia; apply Z2Nat.inj_le; lia | |].
+ intros a Ha. replace a with (y_tm cx + 2 * ((mp - 1) * y_idl cx) + (a - (y_tm cx + 2 * ((mp - 1) * y_idl cx)))) by lia.
apply Hzero. lia.
+ intros a Ha Hna. rewrite LenTM, Z2Nat.id in Ha by lia. apply Hout; [lia | cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 4%nat 6%nat; lia|]; split; [septac HSEP 4%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [lia|]; exact I | lia]. }
split; [exact HI|]. split; [lia|]. split; [lia|]. split; [rewrite <- DvLI; exact HLI1|]. split; [rewrite <- DvLM; exact HLM0|].
split; [lia|]. split; [lia|].
split; [rewrite Hkeep by reflexivity; rewrite (HK 22%bv) by (inl); exact H22|].
split; [rewrite Hkeep by reflexivity; rewrite (HK 23%bv) by (inl); exact H23|].
split; [rewrite Hkeep by reflexivity; exact Q24|].
split; [rewrite Hkeep by reflexivity; exact Q26|].
split; [rewrite Hkeep by reflexivity; exact Q27|].
rewrite Hkeep by reflexivity; exact Q25.
Qed.
Lemma tmiss_seg : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c,
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X -> lzw_inv (y_idl cx) (y_nP cx) X ->
tmiss_pre cx regs s1 q ->
la_s X < s1 <= y_nP cx - 1 -> 0 <= q < 4096 -> 0 <= c < y_idl cx -> val_mem ubs2segs memc (y_img cx + s1) 1 c ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs' mem' o,
c' = mkCfg (mkst regs' (Z_to_bv 64 (tmo_pc o)) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ tabove_eq cx memc mem' /\
tmo_post cx X s1 q c regs' mem' o).
Proof.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c HCX HRG HSEP HBL HWIN HWT HJ HFX HGA HT HI HPRE Hs1 Hq Hc HC.
assert (Hdp : la_dp X <= 4096).
{ destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_dp]. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdp & _). lia. }
destruct (Z.eq_dec (la_dp X) 4096) as [Hfull | Hnf].
- eapply tmiss_full; eassumption.
- destruct (Z.eq_dec (nth (Z.to_nat q) (la_LM X) 0) 0) as [HLM0 | HLM1].
+ destruct (Z.eq_dec (nth (Z.to_nat q) (la_LI X) 0) 0) as [HLI0 | HLI1].
* eapply tmiss_first; try eassumption. lia.
* eapply tmiss_sw; try eassumption. lia.
+ eapply tmiss_map; try eassumption. lia.
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
