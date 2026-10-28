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
YI00 YI02 YI01 YI07 YI03 YI04 YI06 YI5a UI2a.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition tin_facts (b : bool) : list (nat * afact) :=
[ (10%nat, mkAF 0 4095 0); (12%nat, mkAF 4096 CEIL_MAX 0); (15%nat, mkAF 1 100000000 0);
(22%nat, mkAF 1 99999999 0); (16%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX - 100000000) (2 ^ 64 - 4097) 0);
(44%nat, mkAF 0 255 0); (45%nat, mkAF 4096 CEIL_MAX 1); (46%nat, mkAF 0 4095 0); (47%nat, mkAF 4096 CEIL_MAX 0); (48%nat, mkAF 0 255 0);
(49%nat, mkAF 4096 CEIL_MAX 1); (50%nat, mkAF 0 2046 0) ]
++ (if b then [ (51%nat, mkAF 4096 CEIL_MAX 1); (52%nat, mkAF 0 4095 0) ] else []).
Definition tin_X : sv := SAluw ALU_ADD (SMd M_MUL (SOff 50%nat (-1)) (SOff 20%nat 0)) (SLit 0).
Definition tin_Y : sv := SAluw ALU_ADD (SAlu ALU_ADD tin_X (SOff 44%nat 0)) (SLit 0).
Definition tin_alias (b : bool) : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 35%nat 0) (SAlu ALU_SLL (SOff 10%nat 0) (SLit 1)), SOff 45%nat 0);
(SAlu ALU_ADD (SOff 34%nat 0) (SOff 10%nat 0), SOff 47%nat 0);
(SAlu ALU_ADD (SOff 33%nat 0) (SAlu ALU_SLL (SOff 10%nat 0) (SLit 1)), SOff 49%nat 0) ]
++ (if b then [ (SAlu ALU_ADD (SOff 36%nat 0) (SAlu ALU_SLL tin_Y (SLit 1)), SOff 51%nat 0) ] else []).
Definition tin_conds (e b : bool) : list acond :=
[ mkAC (if e then BC_LTU else BC_GEU) (SOff 44%nat 0) (SOff 20%nat 0);
mkAC BC_GEU (SOff 45%nat 0) (SOff 35%nat 0); mkAC BC_GEU (SOff 47%nat 0) (SOff 34%nat 0); mkAC BC_GEU (SOff 49%nat 0) (SOff 33%nat 0) ]
++ (if b then [ mkAC BC_GEU (SOff 51%nat 0) (SOff 36%nat 0);
mkAC BC_EQ (SMdw M_MUL (SOff 50%nat (-1)) (SOff 20%nat 0)) (SMd M_MUL (SOff 50%nat (-1)) (SOff 20%nat 0));
mkAC BC_EQ (SAluw ALU_ADD tin_X (SOff 44%nat 0)) (SAlu ALU_ADD tin_X (SOff 44%nat 0));
mkAC BC_NE (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 51%nat 0) (SOff 36%nat 0)) (SAlu ALU_SLT tin_Y (SLit 0))) (SLit 1)) (SLit 0) ] else []).
Definition tin_img_region : YQ0b.region :=
YQ0b.mkRegion (Some 12%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 44%nat 0))].
Definition tin_regions (b : bool) : smem :=
[ tin_img_region; reg16 45 46 false; reg8 47 48 false; reg16 49 50 false ] ++ (if b then [reg16 51 52 false] else []).
Definition ss_tin (e b : bool) : sstate :=
tlzw_ss TPC_INNER sr_atoms false (tin_regions b) (tin_facts b) (tin_conds e b) (tin_alias b).
Inductive tin_out :=
| TIO_eidx
| TIO_cont (q' : Z)
| TIO_emitc (q' : Z)
| TIO_miss (c : Z).
Definition tio_pc (o : tin_out) : Z :=
match o with TIO_eidx => TPC_EIDX | TIO_cont _ => TPC_INNER | TIO_emitc _ => TPC_EMITC | TIO_miss _ => TPC_MISS end.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition tin_pre (cx : lzw_tcx) (regs : bvmap 5 word) (s1 q : Z) : Prop :=
getr regs 22 = Z_to_bv 64 s1 /\ getr regs 10 = Z_to_bv 64 q /\ getr regs 12 = Z_to_bv 64 (y_img cx + s1) /\
getr regs 15 = Z_to_bv 64 (y_nP cx - s1) /\
getr regs 11 = Z_to_bv 64 (y_nP cx - 1) /\ getr regs 16 = Z_to_bv 64 (y_nimg cx - (s1 - 1)).
Definition tio_post (cx : lzw_tcx) (X : lzw_abs) (s1 q : Z) (memc : word -> option byte) (regs' : bvmap 5 word) (o : tin_out) : Prop :=
let nP := y_nP cx in let idl := y_idl cx in
match o with
| TIO_eidx => True
| TIO_cont q' => tin_pre cx regs' (s1 + 1) q' /\ 0 < q' < 4096 /\ s1 + 1 <= nP - 1
| TIO_emitc q' => getr regs' 22 = Z_to_bv 64 (nP - 1) /\ getr regs' 10 = Z_to_bv 64 q' /\ 0 < q' < 4096 /\ s1 = nP - 1
| TIO_miss c => getr regs' 22 = Z_to_bv 64 s1 /\ getr regs' 10 = Z_to_bv 64 q /\ getr regs' 17 = Z_to_bv 64 (y_lm cx + 2 * q) /\
getr regs' 14 = Z_to_bv 64 (y_li cx + 2 * q) /\ getr regs' 12 = Z_to_bv 64 (y_img cx + s1) /\
getr regs' 23 = Z_to_bv 64 (2 * q) /\ getr regs' 13 = Z_to_bv 64 q /\
0 <= c < idl /\ val_mem ubs2segs memc (y_img cx + s1) 1 c
end.
Ltac Ucondg := match goal with Hc : branch_taken _ _ _ = _ |- _ => Ucond Hc end.
Lemma tinner_iter : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q,
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X -> lzw_inv (y_idl cx) (y_nP cx) X ->
tin_pre cx regs s1 q ->
la_s X < s1 <= y_nP cx - 1 -> 0 <= q < 4096 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 TPC_INNER) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs' mem' o,
c' = mkCfg (mkst regs' (Z_to_bv 64 (tio_pc o)) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\
(forall x, mem' x = memc x) /\
tlzw_regs_fix regs' cx /\ tio_post cx X s1 q memc regs' o).
Proof.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q
HCX HRG HSEP HBL HWIN HJ HF HG HT HI (H22 & H10 & H12 & H15 & H11 & H16) Hs1 Hq.
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
destruct (val_mem1 ubs2segs memc (y_img cx + s1)) as (C & HCv & HC); [apply Pimg; lia|]. change (2 ^ 8) with 256 in HCv.
assert (Plc : forall i, 0 <= i < 4096 -> present memc (y_lc cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_lc cx) 4096 i HH ltac:(apply HBt; cbv; tauto) ltac:(lia))). }
destruct (val_mem1 ubs2segs memc (y_lc cx + q)) as (vLC & HvLCv & HvLC); [apply Plc; lia|]. change (2 ^ 8) with 256 in HvLCv.
destruct (LI_read (y_idl cx) (y_nP cx) _ q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI.
destruct (LM_read (y_idl cx) (y_nP cx) _ q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM.
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
destruct (arr16_nthZ ubs2segs memc (y_li cx) LI q ALI ltac:(lia) HqLI) as [VLI _].
destruct (arr16_nthZ ubs2segs memc (y_lm cx) LM q ALM ltac:(lia) HqLM) as [VLM _].
fold vLI in VLI. fold vLM in VLM.
assert (DvLI : vLI = nth (Z.to_nat q) LI 0) by reflexivity. assert (DvLM : vLM = nth (Z.to_nat q) LM 0) by reflexivity.
clearbody vLI vLM.
remember (C <? y_idl cx) as e eqn:He.
assert (HeT : e = true -> C < y_idl cx) by (intros ->; symmetry in He; apply Z.ltb_lt in He; exact He).
assert (HeF : e = false -> y_idl cx <= C) by (intros ->; symmetry in He; apply Z.ltb_ge in He; exact He).
remember (e && negb (vLM =? 0)) as b eqn:Hb.
assert (HbT : b = true -> e = true /\ 1 <= vLM /\ C < y_idl cx).
{ intros ->. symmetry in Hb. apply andb_prop in Hb as [B1 B2]. rewrite B1 in HeT. specialize (HeT eq_refl).
destruct (Z.eqb_spec vLM 0); [discriminate|]. split; [exact B1|]. lia. }
assert (HbF : b = false -> e = true -> vLM = 0).
{ intros -> He1. rewrite He1 in Hb. cbn in Hb. symmetry in Hb. apply Bool.negb_false_iff in Hb. apply Z.eqb_eq in Hb. exact Hb. }
remember ((vLM - 1) * y_idl cx + C) as j eqn:Hj.
assert (HTMj : b = true -> (Z.to_nat j < length TM)%nat /\ 0 <= nth (Z.to_nat j) TM 0 < 4096 /\ j + 1 <= 2049 * y_idl cx /\ 0 <= j).
{ intros Hbt. destruct (HbT Hbt) as (_ & Hm1 & HCi).
destruct (TM_read (y_idl cx) (y_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) vLM C ltac:(lia) HI ltac:(cbn; lia) ltac:(lia)) as (T1 & T2 & T3).
cbn [la_TM] in T1, T2. subst j. split; [exact T1|]. split; [exact T2|]. split; [exact T3 |].
apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; lia | lia]. }
assert (Hj21 : b = true -> 2 * j + 2 <= 4098 * y_idl cx /\ j < 2 ^ 20).
{ intros Hbt. destruct (HTMj Hbt) as (_ & _ & T3 & _). assert (2049 * y_idl cx <= 2049 * 256) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
remember (nth (Z.to_nat j) TM 0) as vTM eqn:HvTM.
assert (VTM : b = true -> val_mem ubs2segs memc (y_tm cx + 2 * j) 2 vTM).
{ intros Hbt. destruct (HTMj Hbt) as (T1 & _ & _ & T4). rewrite HvTM. exact (proj1 (arr16_nthZ ubs2segs memc (y_tm cx) TM j ATM T4 T1)). }
remember [Z_to_bv 64 C; Z_to_bv 64 (y_li cx + 2 * q); Z_to_bv 64 vLI; Z_to_bv 64 (y_lc cx + q); Z_to_bv 64 vLC;
Z_to_bv 64 (y_lm cx + 2 * q); Z_to_bv 64 vLM; Z_to_bv 64 (y_tm cx + 2 * j); Z_to_bv 64 vTM] as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
assert (HE44 : ew E 44 = Z_to_bv 64 C) by (rewrite HE0, <- (Nat.add_0_r 44), (TE_more regs _ _ _ _ more 0), Hmore; reflexivity).
assert (HE45 : ew E 45 = Z_to_bv 64 (y_li cx + 2 * q)) by (rewrite HE0; change 45%nat with (44 + 1)%nat; rewrite (TE_more regs _ _ _ _ more 1), Hmore; reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 vLI) by (rewrite HE0; change 46%nat with (44 + 2)%nat; rewrite (TE_more regs _ _ _ _ more 2), Hmore; reflexivity).
assert (HE47 : ew E 47 = Z_to_bv 64 (y_lc cx + q)) by (rewrite HE0; change 47%nat with (44 + 3)%nat; rewrite (TE_more regs _ _ _ _ more 3), Hmore; reflexivity).
assert (HE48 : ew E 48 = Z_to_bv 64 vLC) by (rewrite HE0; change 48%nat with (44 + 4)%nat; rewrite (TE_more regs _ _ _ _ more 4), Hmore; reflexivity).
assert (HE49 : ew E 49 = Z_to_bv 64 (y_lm cx + 2 * q)) by (rewrite HE0; change 49%nat with (44 + 5)%nat; rewrite (TE_more regs _ _ _ _ more 5), Hmore; reflexivity).
assert (HE50 : ew E 50 = Z_to_bv 64 vLM) by (rewrite HE0; change 50%nat with (44 + 6)%nat; rewrite (TE_more regs _ _ _ _ more 6), Hmore; reflexivity).
assert (HE51 : ew E 51 = Z_to_bv 64 (y_tm cx + 2 * j)) by (rewrite HE0; change 51%nat with (44 + 7)%nat; rewrite (TE_more regs _ _ _ _ more 7), Hmore; reflexivity).
assert (HE52 : ew E 52 = Z_to_bv 64 vTM) by (rewrite HE0; change 52%nat with (44 + 8)%nat; rewrite (TE_more regs _ _ _ _ more 8), Hmore; reflexivity).
pose proof (TE_sp regs cx lp dp mp more HF) as HE2. pose proof (TE_g regs cx lp dp mp more HF) as HE8.
pose proof (TE_idl regs cx lp dp mp more HF) as HE20. pose proof (TE_ti regs cx lp dp mp more) as HE32.
pose proof (TE_lm regs cx lp dp mp more) as HE33. pose proof (TE_lc regs cx lp dp mp more) as HE34.
pose proof (TE_li regs cx lp dp mp more) as HE35. pose proof (TE_tm regs cx lp dp mp more) as HE36.
pose proof (TE_img regs cx lp dp mp more) as HE38. pose proof (TE_nP regs cx lp dp mp more) as HE39.
pose proof (TE_nimg regs cx lp dp mp more) as HE40.
rewrite <- HE0 in HE2, HE8, HE20, HE32, HE33, HE34, HE35, HE36, HE38, HE39, HE40. unfold y_nimg in HE40.
unfold y_nimg in H16.
assert (HE22 : ew E 22 = Z_to_bv 64 s1) by (rewrite HE0, (TE_reg regs _ _ _ _ more 22%bv 22) by reflexivity; exact H22).
assert (HE10 : ew E 10 = Z_to_bv 64 q) by (rewrite HE0, (TE_reg regs _ _ _ _ more 10%bv 10) by reflexivity; exact H10).
assert (HE12 : ew E 12 = Z_to_bv 64 (y_img cx + s1)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 12%bv 12) by reflexivity; exact H12).
assert (HE15 : ew E 15 = Z_to_bv 64 (y_nP cx - s1)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 15%bv 15) by reflexivity; exact H15).
assert (HE11 : ew E 11 = Z_to_bv 64 (y_nP cx - 1)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 11%bv 11) by reflexivity; exact H11).
assert (HE16 : ew E 16 = Z_to_bv 64 (2 ^ 64 - 1 - y_img cx - (s1 - 1))) by (rewrite HE0, (TE_reg regs _ _ _ _ more 16%bv 16) by reflexivity; exact H16).
Local Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (tcx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app tcx_tabs fst snd zz_disj y_tisz y_tmsz y_cap cap] in Hs; lia.
assert (Hp0 : b = true -> 0 <= (vLM - 1) * y_idl cx <= j).
{ intros Hbt. destruct (HbT Hbt) as (_ & Hm1 & HCi).
assert (0 <= (vLM - 1) * y_idl cx) by (apply Z.mul_nonneg_nonneg; lia). rewrite Hj. lia. }
assert (HUX : b = true -> U E tin_X = (vLM - 1) * y_idl cx).
{ intros Hbt. destruct (HbT Hbt) as (_ & Hm1 & HCi). destruct (HTMj Hbt) as (_ & _ & T3 & T4). specialize (Hj21 Hbt). specialize (Hp0 Hbt).
unfold tin_X. apply U_sextw_small; [apply (U_mul_row64 E 50 20 vLM (y_idl cx) HE50 HE20); lia | lia]. }
assert (HUY : b = true -> U E tin_Y = j).
{ intros Hbt. destruct (HbT Hbt) as (_ & Hm1 & HCi). destruct (HTMj Hbt) as (_ & _ & T3 & T4). specialize (Hj21 Hbt). specialize (Hp0 Hbt).
unfold tin_Y. apply U_sextw_small; [|lia].
rewrite (U_add_small E tin_X (SOff 44%nat 0) ((vLM - 1) * y_idl cx) C (HUX Hbt) (U_atom E 44 C HE44 ltac:(lia))) by lia. lia. }
assert (HS : st_ok ubs2segs E (ss_tin e b) (mkst regs (Z_to_bv 64 TPC_INNER) memc (seg_rom ubs2segs))).
{ unfold ss_tin, tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more memc TPC_INNER false); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HF.
- exact HG.
- intros X0. discriminate X0.
- lia.
- lia.
- lia.
- destruct b; vm_compute; reflexivity.
- unfold tin_regions. apply Forall_app. split.
+ constructor.
{ unfold region_ok, tin_img_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE12, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE44, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
constructor. { eapply (region_ok_reg16 _ E memc 45 46 false (y_li cx + 2 * q) vLI HE45 HE46); [lia | lia | lia | exact VLI | intros X0; discriminate X0]. }
constructor. { eapply (region_ok_reg8 _ E memc 47 48 false (y_lc cx + q) vLC HE47 HE48); [lia | lia | lia | exact HvLC | intros X0; discriminate X0]. }
constructor. { eapply (region_ok_reg16 _ E memc 49 50 false (y_lm cx + 2 * q) vLM HE49 HE50); [lia | lia | lia | exact VLM | intros X0; discriminate X0]. }
constructor.
+ destruct b; [|constructor]. destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
apply Forall_cons; [|apply Forall_nil].
apply (region_ok_reg16 _ E memc 51 52 false (y_tm cx + 2 * j) vTM HE51 HE52); [lia | lia | lia | exact (VTM eq_refl) | intros X0; discriminate X0].
-
unfold tin_regions. destruct b.
+ destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
cbn [all_disjoint app]; unfold extent_disjoint, tin_img_region, reg8, reg16, gen_region; cbn [r_base r_lo r_hi base_val app].
rewrite HE8, HE12, HE45, HE47, HE49, HE51, !unsigned_lit_small by lia.
split; [septac HSEP 6%nat 7%nat|]. split; [septac HSEP 3%nat 6%nat|]. split; [septac HSEP 2%nat 6%nat|].
split; [septac HSEP 1%nat 6%nat|]. split; [septac HSEP 4%nat 6%nat | exact I].
+ cbn [all_disjoint app]; unfold extent_disjoint, tin_img_region, reg8, reg16, gen_region; cbn [r_base r_lo r_hi base_val app].
rewrite HE8, HE12, HE45, HE47, HE49, !unsigned_lit_small by lia.
split; [septac HSEP 6%nat 7%nat|]. split; [septac HSEP 3%nat 6%nat|]. split; [septac HSEP 2%nat 6%nat|].
split; [septac HSEP 1%nat 6%nat | exact I].
- unfold tin_regions. destruct b.
+ destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, tin_img_region, reg8, reg16; cbn [r_base r_lo r_hi base_val].
rewrite HE12, HE45, HE47, HE49, HE51, !unsigned_lit_small by lia.
split; [split; [septac HSEP 3%nat 7%nat | split; [septac HSEP 2%nat 7%nat | split; [septac HSEP 1%nat 7%nat | split; [septac HSEP 4%nat 7%nat | exact I]]]]|].
split; [split; [septac HSEP 2%nat 3%nat | split; [septac HSEP 1%nat 3%nat | split; [septac HSEP 3%nat 4%nat | exact I]]]|].
split; [split; [septac HSEP 1%nat 2%nat | split; [septac HSEP 2%nat 4%nat | exact I]]|].
split; [split; [septac HSEP 1%nat 4%nat | exact I]|]. split; exact I.
+ cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, tin_img_region, reg8, reg16; cbn [r_base r_lo r_hi base_val].
rewrite HE12, HE45, HE47, HE49, !unsigned_lit_small by lia.
split; [split; [septac HSEP 3%nat 7%nat | split; [septac HSEP 2%nat 7%nat | split; [septac HSEP 1%nat 7%nat | exact I]]]|].
split; [split; [septac HSEP 2%nat 3%nat | split; [septac HSEP 1%nat 3%nat | exact I]]|].
split; [split; [septac HSEP 1%nat 2%nat | exact I]|]. split; exact I.
- unfold tin_facts. apply atoms_ok_app.
+ cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE10, HE12, HE15, HE22, HE16, HE44, HE45, HE46, HE47, HE48, HE49, HE50, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
repeat split; try lia.
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rli3].
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rlm3].
+ destruct b; [|exact I]. destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE51, HE52, !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists j; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3].
- unfold tin_conds. cbn [conds_ok app]. split; [|split; [|split; [|split]]].
+ destruct e.
* specialize (HeT eq_refl). apply (cond_ltu E 44 0 20 0 C (y_idl cx) HE44 HE20); lia.
* specialize (HeF eq_refl). apply (cond_geu E 44 0 20 0 C (y_idl cx) HE44 HE20); lia.
+ apply (cond_geu E 45 0 35 0 (y_li cx + 2 * q) (y_li cx) HE45 HE35); lia.
+ apply (cond_geu E 47 0 34 0 (y_lc cx + q) (y_lc cx) HE47 HE34); lia.
+ apply (cond_geu E 49 0 33 0 (y_lm cx + 2 * q) (y_lm cx) HE49 HE33); lia.
+ destruct b; [|exact I]. destruct (HbT eq_refl) as (_ & Hm1 & HCi). destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
specialize (Hp0 eq_refl).
cbn [conds_ok]. split; [apply (cond_geu E 51 0 36 0 (y_tm cx + 2 * j) (y_tm cx) HE51 HE36); lia|].
split; [apply cond_eq_U; rewrite (U_mulw_row E 50 20 vLM (y_idl cx) HE50 HE20), (U_mul_row64 E 50 20 vLM (y_idl cx) HE50 HE20) by lia; reflexivity|].
split; [apply cond_eq_U;
rewrite (U_addw_small E tin_X (SOff 44%nat 0) ((vLM - 1) * y_idl cx) C (HUX eq_refl) (U_atom E 44 C HE44 ltac:(lia))) by lia;
rewrite (U_add_small E tin_X (SOff 44%nat 0) ((vLM - 1) * y_idl cx) C (HUX eq_refl) (U_atom E 44 C HE44 ltac:(lia))) by lia; reflexivity|].
split; [|exact I]. apply cond_ne_U. rewrite (U_ptrchk E 51 36 tin_Y (y_tm cx + 2 * j) (y_tm cx) j HE51 HE36 (HUY eq_refl)) by lia.
rewrite U_SLit. change (zcanon 0) with 0. lia.
- unfold tin_alias. cbn [alias_ok app]. split; [|split; [|split]].
+ apply (alias_b2i' E 35 10 45 (y_li cx) q HE35 HE10 HE45); lia.
+ apply (alias_add E 34 10 47 (y_lc cx) q HE34 HE10 HE47); lia.
+ apply (alias_b2i' E 33 10 49 (y_lm cx) q HE33 HE10 HE49); lia.
+ destruct b; [|exact I]. destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
cbn [alias_ok]. split; [|exact I].
apply (alias_base_sll1 E 36 51 tin_Y (y_tm cx) j HE36 (HUY eq_refl) HE51); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_INNER) memc (seg_rom ubs2segs))) in HJ.
clear ATI ALM ALI ATM Pimg Plc.
Local Ltac leaf HS HJ HF HE0 o :=
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx), o end;
split; [reflexivity|]; split; [exact HJ|]; split; [mem_unchanged_ro|];
let HK := fresh "HK" in
lazymatch type of HE0 with ?E = Ereg ?regs ?ex =>
pose proof (regs_kept_of_st_ok _ _ _ _ regs ex TREGS_FIXL HS
ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK;
split; [apply (tlzw_regs_fix_kept regs); [exact HF | intros r Hr; apply HK; exact Hr]|];
unfold tio_post, tin_pre; cbn [la_lp la_mp la_dp la_TI la_s y_nimg]
end.
Local Ltac found HS HJ HF HE0 child :=
jrun_to LAWS ubs2tbl_ok HS HJ TPC_EMITC; [wr_ok_tac|];
jbranch ubs2tbl HS; Ucondg;
[ jrun_to LAWS ubs2tbl_ok HS HJ TPC_INNER; [wr_ok_tac|]; leaf HS HJ HF HE0 (TIO_cont child)
| jrun_to LAWS ubs2tbl_ok HS HJ TPC_EMITC; [wr_ok_tac|]; leaf HS HJ HF HE0 (TIO_emitc child) ].
Local Ltac reg_expr HS r tac :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
let Q := fresh "Q" in
pose proof (st_ok_reg segs E1 ss1 ms1 r HS) as Q; eval_sr_get_in Q; rewrite denot_lit_U in Q; rewrite Q; clear Q; f_equal; tac end.
Local Ltac regs_tac HS HE10 q :=
unfold y_nimg; repeat split; try lia;
lazymatch goal with
| |- getr (ms_regs _) ?r = _ =>
first [ treg_val HS r
| reg_expr HS r ltac:(apply (U_sll1_small _ (SOff 10%nat 0) q); [apply (U_atom _ 10 q HE10); lia | lia | lia]) ]
| |- val_mem _ _ _ _ _ => assumption
| |- _ => idtac
end.
Local Ltac lm_subtree b HS HJ HF HE0 vTM C :=
jrun_to LAWS ubs2tbl_ok HS HJ TPC_MISS; [wr_ok_tac|];
jbranch ubs2tbl HS; Ucondg;
[
jrun_to LAWS ubs2tbl_ok HS HJ TPC_MISS; [wr_ok_tac|]; leaf HS HJ HF HE0 (TIO_miss C)
| lazymatch b with
| false => exfalso; lia
| true => jrun_to LAWS ubs2tbl_ok HS HJ TPC_MISS; [wr_ok_tac|];
jbranch ubs2tbl HS; Ucondg;
[ jrun_to LAWS ubs2tbl_ok HS HJ TPC_MISS; [wr_ok_tac|]; leaf HS HJ HF HE0 (TIO_miss C)
| found HS HJ HF HE0 vTM ]
end ].
destruct b.
- destruct (HbT eq_refl) as (He1 & Hm1 & HCi). destruct e; [|discriminate He1]. specialize (HeT eq_refl).
destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl). specialize (Hp0 eq_refl).
jrun_to LAWS ubs2tbl_ok HS HJ TPC_EIDX; [wr_ok_tac|].
jbranch ubs2tbl HS; Ucondg.
+
lm_subtree true HS HJ HF HE0 vTM C; regs_tac HS HE10 q.
+ jrun_to LAWS ubs2tbl_ok HS HJ TPC_EIDX; [wr_ok_tac|].
jbranch ubs2tbl HS; Ucondg.
*   found HS HJ HF HE0 vLI; regs_tac HS HE10 q.
* lm_subtree true HS HJ HF HE0 vTM C; regs_tac HS HE10 q.
- destruct e.
2:{
specialize (HeF eq_refl).
jrun_to LAWS ubs2tbl_ok HS HJ TPC_EIDX; [wr_ok_tac|]. leaf HS HJ HF HE0 TIO_eidx. exact I. }
specialize (HeT eq_refl). specialize (HbF eq_refl eq_refl).
jrun_to LAWS ubs2tbl_ok HS HJ TPC_EIDX; [wr_ok_tac|].
jbranch ubs2tbl HS; Ucondg.
+ lm_subtree false HS HJ HF HE0 vTM C; regs_tac HS HE10 q.
+ jrun_to LAWS ubs2tbl_ok HS HJ TPC_EIDX; [wr_ok_tac|].
jbranch ubs2tbl HS; Ucondg.
* found HS HJ HF HE0 vLI; regs_tac HS HE10 q.
* lm_subtree false HS HJ HF HE0 vTM C; regs_tac HS HE10 q.
Qed.
End S.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
