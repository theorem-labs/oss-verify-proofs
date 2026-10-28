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
YI00 YI02 YI01 YI07 YI03 YI04 YI06 UI2a.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition thead_facts (two ti : bool) : list (nat * afact) :=
[ (22%nat, mkAF 0 99999999 0); (44%nat, mkAF 4096 CEIL_MAX 0); (45%nat, mkAF 0 255 0) ]
++ (if two then [ (46%nat, mkAF 0 255 0) ] else [])
++ (if ti then [ (47%nat, mkAF 0 65535 0); (48%nat, mkAF 4096 CEIL_MAX 1); (49%nat, mkAF 0 4095 0) ] else []).
Definition thead_alias (ti : bool) : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 38 0) (SOff 22 0), SOff 44 0) ]
++ (if ti then [ (SAlu ALU_ADD (SMd M_MUL (SOff 45 0) (SOff 20 0)) (SOff 46 0), SOff 47 0);
(SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SLL (SOff 47 0) (SLit 1)), SOff 48 0) ] else []).
Definition thead_conds (two ti : bool) : list acond :=
[ mkAC BC_LTU (SOff 22 0) (SOff 39 0); mkAC BC_GEU (SOff 44 0) (SOff 38 0);
mkAC (if two then BC_LTU else BC_GEU) (SOff 22 0) (SOff 39 (-1)) ]
++ (if ti then [ mkAC BC_LTU (SOff 45 0) (SOff 20 0); mkAC BC_LTU (SOff 46 0) (SOff 20 0); mkAC BC_GEU (SOff 48 0) (SOff 32 0) ] else []).
Definition timg_region (two : bool) : YQ0b.region :=
YQ0b.mkRegion (Some 44%nat) 0 (if two then 2 else 1) 0 0
(mkChunk 0 (CVal 1 (SOff 45%nat 0)) :: (if two then [mkChunk 1 (CVal 1 (SOff 46%nat 0))] else [])).
Definition thead_regions (two ti : bool) : smem :=
timg_region two :: (if ti then [reg16 48 49 false] else []).
Definition ss_thead (two ti : bool) : sstate :=
tlzw_ss TPC_HEAD (sr_set sr_atoms 11%bv (SOff 39%nat 0)) false (thead_regions two ti) (thead_facts two ti) (thead_conds two ti) (thead_alias ti).
Inductive thead_out :=
| THO_eidx
| THO_emitc (q : Z)
| THO_timiss (c1 c2 : Z)
| THO_inner (q : Z).
Definition tho_pc (o : thead_out) : Z :=
match o with THO_eidx => TPC_EIDX | THO_emitc _ => TPC_EMITC | THO_timiss _ _ => TPC_TIMISS | THO_inner _ => TPC_INNER end.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition tho_post (cx : lzw_tcx) (X : lzw_abs) (memc : word -> option byte) (regs' : bvmap 5 word) (o : thead_out) : Prop :=
let nP := y_nP cx in let idl := y_idl cx in let s := la_s X in
match o with
| THO_eidx => True
| THO_emitc q => getr regs' 22 = Z_to_bv 64 (nP - 1) /\ getr regs' 10 = Z_to_bv 64 q /\ 0 <= q < 4096
| THO_timiss c1 c2 => getr regs' 22 = Z_to_bv 64 (s + 1) /\ getr regs' 10 = Z_to_bv 64 c1 /\
getr regs' 14 = Z_to_bv 64 (y_img cx + s + 1) /\ getr regs' 15 = Z_to_bv 64 (c1 * idl) /\ getr regs' 13 = Z_to_bv 64 (y_ti cx) /\
0 <= c1 < idl /\ 0 <= c2 < idl /\ nth (Z.to_nat (c1 * idl + c2)) (la_TI X) 0 = 0 /\ s + 1 < nP /\
val_mem ubs2segs memc (y_img cx + s + 1) 1 c2
| THO_inner q => getr regs' 22 = Z_to_bv 64 (s + 2) /\ getr regs' 10 = Z_to_bv 64 q /\ getr regs' 12 = Z_to_bv 64 (y_img cx + s + 2) /\
getr regs' 15 = Z_to_bv 64 (nP - 1 - (s + 1)) /\
getr regs' 11 = Z_to_bv 64 (nP - 1) /\ getr regs' 16 = Z_to_bv 64 (y_nimg cx - (s + 1)) /\
0 < q < 4096 /\ s + 1 < nP - 1
end.
Ltac Ucondg := match goal with Hc : branch_taken _ _ _ = _ |- _ => Ucond Hc end.
Ltac reg_val_all :=
repeat split;
lazymatch goal with
| HS : st_ok _ _ _ ?msx |- getr (ms_regs ?msy) ?r = _ => treg_val HS r
| |- _ => first [assumption | reflexivity | lia]
end.
Lemma thead_seg : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X,
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X -> lzw_inv (y_idl cx) (y_nP cx) X ->
getr regs 11 = Z_to_bv 64 (y_nP cx) -> getr regs 22 = Z_to_bv 64 (la_s X) ->
la_s X < y_nP cx ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_HEAD) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs' mem' o,
c' = mkCfg (mkst regs' (Z_to_bv 64 (tho_pc o)) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\
(forall x, mem' x = memc x) /\
tlzw_regs_fix regs' cx /\ tho_post cx X memc regs' o).
Proof.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X
HCX HRG HSEP HBL HWIN HWT HJ HF HG HT HI H11 H22 Hs.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HH.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof HRG as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct HBL as [HBt HBi]. destruct HWIN as [W1 W2].
destruct HT as (ATI & ALM & ALI & ATM).
unfold y_tisz, y_tmsz, y_cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
assert (HMRle : y_MR cx <= 26055).
{ assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (y_idl cx) (y_nP cx) (y_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
assert (Pimg : forall i, 0 <= i < y_nP cx -> present memc (y_img cx + i)).
{ intros i Hi. replace (y_img cx + i) with (y_bi cx + (y_img cx - y_bi cx + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_bi cx) (y_Li cx) (y_img cx - y_bi cx + i) HH HBi ltac:(lia))). }
destruct (val_mem1 ubs2segs memc (y_img cx + s)) as (C1 & HC1v & HC1); [apply Pimg; lia|]. change (2 ^ 8) with 256 in HC1v.
remember (s <? y_nP cx - 1) as two eqn:Htwo.
assert (HC2ex : exists C2, 0 <= C2 < 256 /\ (two = true -> val_mem ubs2segs memc (y_img cx + s + 1) 1 C2)).
{ destruct two.
- symmetry in Htwo. apply Z.ltb_lt in Htwo.
destruct (val_mem1 ubs2segs memc (y_img cx + s + 1)) as (C2 & HC2v & HC2); [replace (y_img cx + s + 1) with (y_img cx + (s + 1)) by lia; apply Pimg; lia|].
exists C2. change (2 ^ 8) with 256 in HC2v. split; [exact HC2v | intros _; exact HC2].
- exists 0. split; [lia | intros X0; discriminate X0]. }
destruct HC2ex as (C2 & HC2v & HC2).
remember (two && (C1 <? y_idl cx) && (C2 <? y_idl cx)) as ti eqn:Hti.
assert (HtiT : ti = true -> two = true /\ C1 < y_idl cx /\ C2 < y_idl cx).
{ intros ->. symmetry in Hti. apply andb_prop in Hti as [B1 B3]. apply andb_prop in B1 as [B1 B2].
apply Z.ltb_lt in B2. apply Z.ltb_lt in B3. auto. }
assert (HtwoT : two = true -> s < y_nP cx - 1) by (intros ->; symmetry in Htwo; apply Z.ltb_lt in Htwo; exact Htwo).
assert (HtwoF : two = false -> s = y_nP cx - 1) by (intros ->; symmetry in Htwo; apply Z.ltb_ge in Htwo; lia).
remember (C1 * y_idl cx + C2) as K eqn:HK0.
assert (HKr : 0 <= K <= 255 * 256 + 255).
{ subst K. split; [apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; lia | lia]|].
assert (C1 * y_idl cx <= 255 * 256) by (apply Z.mul_le_mono_nonneg; lia). lia. }
assert (HTIj : ti = true -> (Z.to_nat K < length TI)%nat /\ 0 <= nth (Z.to_nat K) TI 0 < 4096).
{ intros Ht. destruct (HtiT Ht) as (_ & HC1i & HC2i).
destruct (TI_read (y_idl cx) (y_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) C1 C2 ltac:(lia) HI ltac:(lia) ltac:(lia)) as [T1 T2].
cbn [la_TI] in T1, T2. subst K. exact (conj T1 T2). }
remember (nth (Z.to_nat K) TI 0) as vTI eqn:HvTI.
assert (VTI : ti = true -> val_mem ubs2segs memc (y_ti cx + 2 * K) 2 vTI).
{ intros Ht. destruct (HTIj Ht) as [T1 _]. rewrite HvTI. exact (proj1 (arr16_nthZ ubs2segs memc (y_ti cx) TI K ATI ltac:(lia) T1)). }
assert (HKsz : ti = true -> 2 * K + 2 <= 2 * y_idl cx * y_idl cx).
{ intros Ht. destruct (HTIj Ht) as [T1 _]. rewrite LenTI in T1.
assert (K < y_idl cx * y_idl cx) by (apply Z2Nat.inj_lt; [lia | nia | exact T1]). nia. }
assert (PTI : forall i, 0 <= i < 2 * y_idl cx * y_idl cx -> present memc (y_ti cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_ti cx) (2 * y_idl cx * y_idl cx) i HH ltac:(apply HBt; cbv; tauto) Hi)). }
assert (Pg : forall i, 0 <= i < 72 -> present memc (y_g cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_g cx) 72 i HH ltac:(apply HBt; cbv; tauto) Hi)). }
remember [Z_to_bv 64 (y_img cx + s); Z_to_bv 64 C1; Z_to_bv 64 C2; Z_to_bv 64 K; Z_to_bv 64 (y_ti cx + 2 * K); Z_to_bv 64 vTI] as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
assert (HE44 : ew E 44 = Z_to_bv 64 (y_img cx + s)) by (rewrite HE0, <- (Nat.add_0_r 44), (TE_more regs _ _ _ _ more 0), Hmore; reflexivity).
assert (HE45 : ew E 45 = Z_to_bv 64 C1) by (rewrite HE0; change 45%nat with (44 + 1)%nat; rewrite (TE_more regs _ _ _ _ more 1), Hmore; reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 C2) by (rewrite HE0; change 46%nat with (44 + 2)%nat; rewrite (TE_more regs _ _ _ _ more 2), Hmore; reflexivity).
assert (HE47 : ew E 47 = Z_to_bv 64 K) by (rewrite HE0; change 47%nat with (44 + 3)%nat; rewrite (TE_more regs _ _ _ _ more 3), Hmore; reflexivity).
assert (HE48 : ew E 48 = Z_to_bv 64 (y_ti cx + 2 * K)) by (rewrite HE0; change 48%nat with (44 + 4)%nat; rewrite (TE_more regs _ _ _ _ more 4), Hmore; reflexivity).
assert (HE49 : ew E 49 = Z_to_bv 64 vTI) by (rewrite HE0; change 49%nat with (44 + 5)%nat; rewrite (TE_more regs _ _ _ _ more 5), Hmore; reflexivity).
pose proof (TE_sp regs cx lp dp mp more HF) as HE2. pose proof (TE_g regs cx lp dp mp more HF) as HE8.
pose proof (TE_idl regs cx lp dp mp more HF) as HE20. pose proof (TE_ti regs cx lp dp mp more) as HE32.
pose proof (TE_img regs cx lp dp mp more) as HE38. pose proof (TE_nP regs cx lp dp mp more) as HE39.
pose proof (TE_nimg regs cx lp dp mp more) as HE40.
rewrite <- HE0 in HE2, HE8, HE20, HE32, HE38, HE39, HE40. unfold y_nimg in HE40.
assert (HE22 : ew E 22 = Z_to_bv 64 s) by (rewrite HE0, (TE_reg regs _ _ _ _ more 22%bv 22) by reflexivity; exact H22).
assert (HE11 : ew E 11 = Z_to_bv 64 (y_nP cx)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 11%bv 11) by reflexivity; exact H11).
Local Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (tcx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app tcx_tabs fst snd zz_disj y_tisz y_tmsz y_cap cap] in Hs; lia.
assert (HS : st_ok ubs2segs E (ss_thead two ti) (mkst regs (Z_to_bv 64 TPC_HEAD) memc (seg_rom ubs2segs))).
{ unfold ss_thead.
enough (HS0 : st_ok ubs2segs E (tlzw_ss TPC_HEAD sr_atoms false (thead_regions two ti) (thead_facts two ti) (thead_conds two ti) (thead_alias ti))
(mkst regs (Z_to_bv 64 TPC_HEAD) memc (seg_rom ubs2segs))).
{ apply (st_ok_set_reg' ubs2segs E _ _ (11%bv:reg) (SOff 39%nat 0) HS0 eq_refl).
cbn [sv_denot ms_regs]. rewrite HE39, unsigned_lit_small, Z.add_0_r by lia. symmetry. exact H11. }
unfold tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more memc TPC_HEAD false); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HF.
- exact HG.
- intros X0. discriminate X0.
- lia.
- lia.
- lia.
- destruct two, ti; vm_compute; reflexivity.
- unfold thead_regions. apply Forall_cons.
+ unfold region_ok, timg_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE44, unsigned_lit_small by lia. split; [lia|]. split; [destruct two; lia|]. split; [intros o Ho; lia|].
apply Forall_cons.
{ eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC1]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE45, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
destruct two; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | exact (HC2 eq_refl)]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE46, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
+ destruct ti; [|apply Forall_nil]. destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl).
apply Forall_cons; [|apply Forall_nil].
apply (region_ok_reg16 _ E memc 48 49 false (y_ti cx + 2 * K) vTI HE48 HE49); [lia | lia | | exact (VTI eq_refl) | intros X0; discriminate X0].
destruct (HTIj eq_refl) as [_ T2]. lia.
- unfold thead_regions. destruct ti.
+ destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl).
cbn [all_disjoint app]; unfold extent_disjoint, timg_region, reg16, gen_region; cbn [r_base r_lo r_hi base_val app].
rewrite HE8, HE44, HE48, !unsigned_lit_small by lia.
split; [destruct two; septac HSEP 6%nat 7%nat|]. split; [septac HSEP 0%nat 6%nat | exact I].
+ cbn [all_disjoint app]; unfold extent_disjoint, timg_region, gen_region; cbn [r_base r_lo r_hi base_val app].
rewrite HE8, HE44, !unsigned_lit_small by lia. split; [destruct two; septac HSEP 6%nat 7%nat | exact I].
- unfold thead_regions. destruct ti; [|cbn [pairwise_disjoint all_disjoint app]; repeat split].
destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl). destruct two; [|discriminate Htw]. specialize (HtwoT eq_refl).
cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, timg_region, reg16; cbn [r_base r_lo r_hi base_val].
rewrite HE44, HE48, !unsigned_lit_small by lia. split; [split; [septac HSEP 0%nat 7%nat | exact I] | split; exact I].
- unfold thead_facts. apply atoms_ok_app; [|apply atoms_ok_app].
+ cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE22, HE44, HE45, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ destruct two; [|exact I]. cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE46, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
+ destruct ti; [|exact I]. destruct (HTIj eq_refl) as [_ T2]. specialize (HKsz eq_refl).
cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE47, HE48, HE49, !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists K; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rti3].
- unfold thead_conds. cbn [conds_ok app]. split; [|split; [|split]].
+ apply (cond_ltu E 22 0 39 0 s (y_nP cx) HE22 HE39); lia.
+ apply (cond_geu E 44 0 38 0 (y_img cx + s) (y_img cx) HE44 HE38); lia.
+ destruct two.
* specialize (HtwoT eq_refl). apply (cond_ltu E 22 0 39 (-1) s (y_nP cx) HE22 HE39); lia.
* specialize (HtwoF eq_refl). apply (cond_geu E 22 0 39 (-1) s (y_nP cx) HE22 HE39); lia.
+ destruct ti; [|exact I]. destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl). cbn [conds_ok].
split; [apply (cond_ltu E 45 0 20 0 C1 (y_idl cx) HE45 HE20); lia|].
split; [apply (cond_ltu E 46 0 20 0 C2 (y_idl cx) HE46 HE20); lia|].
split; [apply (cond_geu E 48 0 32 0 (y_ti cx + 2 * K) (y_ti cx) HE48 HE32); lia | exact I].
- unfold thead_alias. cbn [alias_ok app]. split.
+ rewrite (alias_add E 38 22 44 (y_img cx) s HE38 HE22 HE44); [reflexivity | lia | lia | lia].
+ destruct ti; [|exact I]. destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). specialize (HKsz eq_refl). cbn [alias_ok].
split; [rewrite HK0 in HE47; apply (alias_mul_add E 45 20 46 47 C1 (y_idl cx) C2 HE45 HE20 HE46 HE47); lia|].
split; [apply (alias_b2i' E 32 47 48 (y_ti cx) K HE32 HE47 HE48); lia | exact I]. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_HEAD) memc (seg_rom ubs2segs))) in HJ.
clear ATI ALM ALI ATM Pimg PTI.
pose proof (HWT (y_g cx, 72) ltac:(cbv; tauto)) as Wg.
Local Ltac wr_tac HE8 Wg HBt := wr_ok_tac.
Local Ltac reg_expr HS r tac :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
let Q := fresh "Q" in
pose proof (st_ok_reg segs E1 ss1 ms1 r HS) as Q; eval_sr_get_in Q; rewrite denot_lit_U in Q; rewrite Q; clear Q; f_equal; tac end.
Local Ltac leaf HS HJ HF HE0 o :=
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx), o end;
split; [reflexivity|]; split; [exact HJ|]; split; [mem_unchanged_ro|];
let HK := fresh "HK" in
lazymatch type of HE0 with ?E = Ereg ?regs ?ex =>
pose proof (regs_kept_of_st_ok _ _ _ _ regs ex TREGS_FIXL HS
ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK;
split; [apply (tlzw_regs_fix_kept regs); [exact HF | intros r Hr; apply HK; exact Hr]|];
unfold tho_post; cbn [la_lp la_mp la_dp la_TI la_s y_nimg]
end.
destruct ti.
-
destruct (HtiT eq_refl) as (Htw & HC1i & HC2i). destruct two; [|discriminate Htw]. specialize (HtwoT eq_refl). destruct (HTIj eq_refl) as [T1 T2].
jrun_to LAWS ubs2tbl_ok HS HJ TPC_TIMISS; [wr_tac HE8 Wg HBt|].
jbranch ubs2tbl HS; Ucondg.
+
jrun_to LAWS ubs2tbl_ok HS HJ TPC_TIMISS; [wr_tac HE8 Wg HBt|].
leaf HS HJ HF HE0 (THO_timiss C1 C2). subst K.
repeat split; try lia.
* treg_val HS (22%bv:reg).
* treg_val HS (10%bv:reg).
* treg_val HS (14%bv:reg).
* reg_expr HS (15%bv:reg) ltac:(apply (U_mul_atoms _ 45 20 C1 (y_idl cx)); [exact HE45 | exact HE20 | lia | lia]).
* treg_val HS (13%bv:reg).
* exact (HC2 eq_refl).
+ jrun_to LAWS ubs2tbl_ok HS HJ TPC_INNER; [wr_tac HE8 Wg HBt|].
jbranch ubs2tbl HS; Ucondg.
* jrun_to LAWS ubs2tbl_ok HS HJ TPC_EMITC; [wr_tac HE8 Wg HBt|].
leaf HS HJ HF HE0 (THO_emitc vTI). repeat split; try lia; [treg_val HS (22%bv:reg) | treg_val HS (10%bv:reg)].
* jrun_to LAWS ubs2tbl_ok HS HJ TPC_INNER; [wr_tac HE8 Wg HBt|].
leaf HS HJ HF HE0 (THO_inner vTI). repeat split; try lia.
-- treg_val HS (22%bv:reg).
-- treg_val HS (10%bv:reg).
-- treg_val HS (12%bv:reg).
-- reg_expr HS (15%bv:reg) ltac:(apply (U_tcnt _ 39 22 (y_nP cx) s); [exact HE39 | exact HE22 | lia | lia | lia]).
-- treg_val HS (11%bv:reg).
-- reg_expr HS (16%bv:reg) ltac:(apply (U_tgrd _ 22 40 s (2 ^ 64 - 1 - y_img cx)); [exact HE22 | exact HE40 | lia | pose proof alloc_ceiling_lt; lia | lia]).
- destruct two.
+
specialize (HtwoT eq_refl).
jrun_to LAWS ubs2tbl_ok HS HJ TPC_EIDX; [wr_tac HE8 Wg HBt|].
jbranch ubs2tbl HS; Ucondg.
* jrun_to LAWS ubs2tbl_ok HS HJ TPC_EIDX; [wr_tac HE8 Wg HBt|]. leaf HS HJ HF HE0 THO_eidx. exact I.
* jrun_to LAWS ubs2tbl_ok HS HJ TPC_EIDX; [wr_tac HE8 Wg HBt|].
jbranch ubs2tbl HS; Ucondg.
-- jrun_to LAWS ubs2tbl_ok HS HJ TPC_EIDX; [wr_tac HE8 Wg HBt|]. leaf HS HJ HF HE0 THO_eidx. exact I.
-- exfalso. symmetry in Hti. apply Bool.andb_false_iff in Hti as [Hti|Hti]; [apply Bool.andb_false_iff in Hti as [Hti|Hti]; [discriminate|]|];
apply Z.ltb_ge in Hti; lia.
+
specialize (HtwoF eq_refl).
jrun_to LAWS ubs2tbl_ok HS HJ TPC_EIDX; [wr_tac HE8 Wg HBt|].
jbranch ubs2tbl HS; Ucondg.
* jrun_to LAWS ubs2tbl_ok HS HJ TPC_EIDX; [wr_tac HE8 Wg HBt|]. leaf HS HJ HF HE0 THO_eidx. exact I.
* jrun_to LAWS ubs2tbl_ok HS HJ TPC_EMITC; [wr_tac HE8 Wg HBt|].
leaf HS HJ HF HE0 (THO_emitc C1). repeat split; try lia; [treg_val HS (22%bv:reg) | treg_val HS (10%bv:reg)].
Qed.
End S.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
