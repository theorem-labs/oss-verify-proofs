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
YI06 UI5b YI09 YI08 YI0t YI0r YI0o YI0s UI3p UI3n UI3o UI3k
UI1u UI1t YI62.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u UI30 UI3e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0h YI0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac inl' := repeat (first [ left; reflexivity | right ]).
Ltac inl := cbv; inl'.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition texit_facts : list (nat * afact) := [ (44%nat, mkAF 4096 CEIL_MAX 1) ].
Definition texit_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 37%nat 0) (SAlu ALU_SLL (SOff 41%nat 0) (SLit 1)), SOff 44%nat 0) ].
Definition texit_conds : list acond := [ mkAC BC_GEU (SOff 44%nat 0) (SOff 37%nat 0) ].
Definition trodata_region : YP09.region :=
YP09.mkRegion None ubs0_D_const_u64_0x0101010101010102 (ubs0_D_const_u64_0x0101010101010102 + 8) 0 0
[mkChunk ubs0_D_const_u64_0x0101010101010102 (CImg 8)].
Definition tpresult_region : YP09.region := YP09.mkRegion (Some 18%nat) 0 16 0 12 [].
Definition ss_texit : sstate := tlzw_ss TPC_EXIT sr_atoms true [regw 44 2; trodata_region] texit_facts texit_conds texit_alias.
Lemma trodata_bytes : forall i, 0 <= i < 8 -> exists b,
seg_rom ubs0segs (Z_to_bv 64 (ubs0_D_const_u64_0x0101010101010102 + i)) = Some b.
Proof using.
intros i Hi.
assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; eexists; reflexivity.
Qed.
Lemma trodata_in_img : forall i, 0 <= i < 8 -> in_img ubs0_msyms (ubs0_D_const_u64_0x0101010101010102 + i).
Proof using.
intros i Hi. unfold in_img. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|].
eexists. split; [left; reflexivity|].
lazymatch goal with |- bv_unsigned ?x <= _ < bv_unsigned ?x' + bv_unsigned ?y =>
let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v;
let w := eval vm_compute in (bv_unsigned y) in change (bv_unsigned y) with w end.
pose proof (eq_refl : ubs0_D_const_u64_0x0101010101010102 = 0x103f0). lia.
Qed.
Lemma tperm_cbl : forall (r2 r1 ti lm lc li tm ld g : Z * Z) (B0 : list (Z * Z)),
Permutation ([r2; r1] ++ ([ti; lm; lc; li; tm; ld; g] ++ B0)) (r1 :: ld :: (r2 :: [ti; lm; lc; li; tm; g] ++ B0)).
Proof using.
intros. cbn [app]. eapply perm_trans; [apply perm_swap|]. apply perm_skip.
change (r2 :: ti :: lm :: lc :: li :: tm :: ld :: g :: B0) with ([r2; ti; lm; lc; li; tm] ++ ld :: (g :: B0)).
change (ld :: r2 :: ti :: lm :: lc :: li :: tm :: g :: B0) with (ld :: [r2; ti; lm; lc; li; tm] ++ (g :: B0)).
apply Permutation_sym. apply Permutation_middle.
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Definition tepi_postV (cx : lzw_tcx) (STK sp0 : Z) FP L A mem md (B0 : list (Z * Z)) (regs : bvmap 5 word)
(mem1 : word -> option byte) (codes : list Z) (c' : config) : Prop :=
exists L7 A7 regs7 mem7 md7 (r : Z),
c' = mkCfg (mkst regs7 (Z_to_bv 64 TPC_CLEAN) mem7 (seg_rom ubs0segs)) md7 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L7 A7 mem7 md7 /\ st_init_done A7 = true /\
getr regs7 2 = Z_to_bv 64 (y_sp cx) /\ getr regs7 3 = getr regs 3 /\ getr regs7 4 = getr regs 4 /\
getr regs7 8 = Z_to_bv 64 (y_g cx) /\ getr regs7 9 = Z_to_bv 64 r /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (y_sp cx - 8192 <= a < y_sp cx) -> ~ (y_pR cx <= a < y_pR cx + 12) ->
mbyte ubs0segs mem7 a = mbyte ubs0segs mem1 a) /\
(forall b m i, In (b, m) B0 -> 0 <= i < m -> mbyte ubs0segs mem7 (b + i) = mbyte ubs0segs mem1 (b + i)) /\
(forall i, 0 <= i < 48 -> mbyte ubs0segs mem7 (y_g cx + i) = mbyte ubs0segs mem1 (y_g cx + i)) /\
((r = 0 /\
exists bb Lbb M,
Permutation (blocks L7 A7) ((bb, Lbb) :: tcx_tabs cx ++ B0) /\
wtok' STK sp0 FP (blocks L A) (bb, Lbb) /\ bb <> 0 /\
word_mem ubs0segs mem7 (y_pR cx) bb /\ val_mem ubs0segs mem7 (y_pR cx + 8) 4 M /\ 1 <= M <= Lbb /\
M <= 2 * y_nP cx + 16 /\
garr8 ubs0segs mem7 bb (raster_of (y_idl cx) (y_icl cx) codes) /\ M = Z.of_nat (length (raster_of (y_idl cx) (y_icl cx) codes)))
\/ (r = 2 /\ Permutation (blocks L7 A7) (tcx_tabs cx ++ B0) /\
(forall a, y_pR cx <= a < y_pR cx + 12 -> mbyte ubs0segs mem7 a = mbyte ubs0segs mem1 a))).
Definition TPC_EPIB : Z := ubs0_A_LZW_GenerateStream + 0x670.
Definition tepi_midV (cx : lzw_tcx) (STK sp0 : Z) FP L A mem md (B0 : list (Z * Z)) (regs : bvmap 5 word)
(mem1 : word -> option byte) (lp : Z) (codes : list Z) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (res1 res2 : Z),
let n1 := 12 * (lp + 1) / 8 + 3 in let n2 := 384 * (lp + 1) / 255 + 4 in
c' = mkCfg (mkst regs2 (Z_to_bv 64 TPC_EPIB) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\ st_init_done A2 = true /\
getr regs2 2 = Z_to_bv 64 (y_sp cx) /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
getr regs2 8 = Z_to_bv 64 (y_g cx) /\ getr regs2 9 = Z_to_bv 64 2 /\ getr regs2 18 = Z_to_bv 64 (y_pR cx) /\
getr regs2 19 = Z_to_bv 64 (y_icl cx) /\ getr regs2 20 = Z_to_bv 64 (y_idl cx) /\ getr regs2 21 = Z_to_bv 64 res2 /\
getr regs2 22 = Z_to_bv 64 (lp + 1) /\ getr regs2 23 = Z_to_bv 64 res1 /\ val_mem ubs0segs mem2 (y_g cx + 40) 8 (y_ld cx) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (y_sp cx - 8192 <= a < y_sp cx) -> mbyte ubs0segs mem2 a = mbyte ubs0segs mem1 a) /\
(forall b m i, In (b, m) B0 -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs mem1 (b + i)) /\
(forall i, 0 <= i < 48 -> mbyte ubs0segs mem2 (y_g cx + i) = mbyte ubs0segs mem1 (y_g cx + i)) /\
Permutation (blocks L2 A2) (nz [(res2, n2); (res1, n1)] ++ (tcx_tabs cx ++ B0)) /\
(forall b, In b (nz [(res2, n2); (res1, n1)]) -> wtok' STK sp0 FP (blocks L A) b /\ fst b <> 0) /\
(res1 <> 0 -> 4096 <= res1 /\ res1 + n1 <= alloc_ceiling /\ res1 mod 16 = 0) /\
(res2 <> 0 -> 4096 <= res2 /\ res2 + n2 <= alloc_ceiling /\ res2 mod 16 = 0) /\
arr16 ubs0segs mem2 (y_ld cx) codes.
Lemma ttmp_free_pre : forall L1 A1 m1 md1 (p n : Z) rest R STK sp0 FP bl0,
heap_ok MR L1 A1 m1 md1 -> Permutation (blocks L1 A1) (nz ((p, n) :: rest) ++ R) ->
(forall b, In b (nz ((p, n) :: rest)) -> wtok' STK sp0 FP bl0 b /\ fst b <> 0) -> 0 < n -> alloc_ceiling + STK <= sp0 ->
p = 0 \/ (In (p, n) (blocks L1 A1) /\ ftok FP bl0 (p, n)).
Proof using LAWS.
intros L1 A1 m1 md1 p n rest R STK sp0 FP bl0 HH HP HT Hn Hsp.
destruct (tfree_pre_case p n rest R (blocks L1 A1) (fun b => wtok' STK sp0 FP bl0 b /\ fst b <> 0) HP HT) as [Hz | [Hin [Hw _]]]; [left; exact Hz | right].
split; [exact Hin|]. eapply ftok_of_wtok; [exact Hw | | exact Hsp].
exact (proj1 (proj2 (heap_blocks_range _ _ LAWS _ _ _ _ p n HH Hin Hn))).
Qed.
Lemma tlzw_epiAV :
forall cx STK sp0 FP L A mem md L6 A6 md6 (regs : bvmap 5 word) (mem1 : word -> option byte) (lp dp mp : Z) (B0 : list (Z * Z)) (LD : list Z),
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_win STK sp0 cx ->
journal ubs0_msyms MR STK sp0 FP L A mem md L6 A6 mem1 md6 -> st_init_done A6 = true ->
Permutation (blocks L6 A6) (tcx_tabs cx ++ B0) ->
(forall b, In b (tcx_tabs cx) -> wtok' STK sp0 FP (blocks L A) b) ->
tlzw_regs_fix regs cx -> gen_at mem1 cx lp dp mp ->
0 <= lp -> lp + 1 <= y_cap cx -> 4 <= dp <= 4096 -> 1 <= mp <= 2047 ->
lzw_rodata_ok mem1 -> y_sp cx + 112 <= y_pR cx -> y_pR cx + 16 <= sp0 ->
arr16 ubs0segs mem1 (y_ld cx) LD -> Z.of_nat (length LD) = lp ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_EXIT) mem1 (seg_rom ubs0segs)) md6)
(tepi_midV cx STK sp0 FP L A mem md B0 regs mem1 lp (LD ++ [y_idl cx + 1])).
Proof using IMG.
intros cx STK sp0 FP L A mem md L6 A6 md6 regs mem1 lp dp mp B0 LD
HCX HRG HSEP HWIN HJ Hid HB HWT HF HGA Hlp0 Hlp1 Hdp Hmp HRO HpRhi HpRhi2 ALD LenLD.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof (proj1 HJ) as HH.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof HRG as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct HWIN as [W1 W2].
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
unfold y_tisz, y_tmsz, y_cap, cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
assert (HMRle : y_MR cx <= 26055).
{ assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
assert (Hlp27 : lp + 1 <= 134217727) by lia.
assert (Hspm : y_sp cx mod 16 = 0) by exact Hal16.
assert (Htp0 : getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms)) by (destruct HF as (_ & _ & _ & _ & _ & _ & _ & H4 & _); exact H4).
assert (G9 : getr regs 9 = Z_to_bv 64 2) by (destruct HF as (_ & _ & _ & _ & _ & _ & H9 & _); exact H9).
pose proof (Z.div_mod (12 * (lp + 1)) 8 ltac:(lia)) as Hdm8. pose proof (Z.mod_pos_bound (12 * (lp + 1)) 8 ltac:(lia)) as Hmb8.
remember (12 * (lp + 1) / 8) as q8 eqn:Hq8. remember ((12 * (lp + 1)) mod 8) as r8 eqn:Hr8. clear Hr8. apply hideP_i in Hq8.
pose proof (Z.div_mod (384 * (lp + 1)) 255 ltac:(lia)) as Hdm255. pose proof (Z.mod_pos_bound (384 * (lp + 1)) 255 ltac:(lia)) as Hmb255.
remember (384 * (lp + 1) / 255) as q255 eqn:Hq255. remember ((384 * (lp + 1)) mod 255) as r255 eqn:Hr255. clear Hr255. apply hideP_i in Hq255.
remember [Z_to_bv 64 (y_ld cx + 2 * lp)] as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE44 : ew E 44 = Z_to_bv 64 (y_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 44), (TE_more regs _ _ _ _ more 0), Hmore; reflexivity).
pose proof (TE_sp regs cx lp dp mp more HF) as HE2. pose proof (TE_g regs cx lp dp mp more HF) as HE8.
pose proof (TE_idl regs cx lp dp mp more HF) as HE20. pose proof (TE_pR regs cx lp dp mp more HF) as HE18. pose proof (TE_icl regs cx lp dp mp more HF) as HE19.
pose proof (TE_ld regs cx lp dp mp more) as HE37. pose proof (TE_lp regs cx lp dp mp more) as HE41.
pose proof (TE_ti regs cx lp dp mp more) as HE32. pose proof (TE_lm regs cx lp dp mp more) as HE33.
pose proof (TE_lc regs cx lp dp mp more) as HE34. pose proof (TE_li regs cx lp dp mp more) as HE35. pose proof (TE_tm regs cx lp dp mp more) as HE36.
rewrite <- HE0 in HE2, HE8, HE20, HE18, HE19, HE37, HE41, HE32, HE33, HE34, HE35, HE36.
assert (HE2u : bv_unsigned (ew E 2) = y_sp cx) by (rewrite HE2; apply unsigned_lit_small; lia).
assert (LDin : In (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) (blocks L6 A6)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; left; cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; inl']. }
assert (Gin : In (y_g cx, 72) (blocks L6 A6)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; left; inl]. }
assert (Pld : forall i, 0 <= i < 2 -> present mem1 (y_ld cx + 2 * lp + i)).
{ intros i Hi. replace (y_ld cx + 2 * lp + i) with (y_ld cx + (2 * lp + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx)) (2 * lp + i) HH LDin ltac:(lia))). }
assert (Pg : forall i, 0 <= i < 72 -> present mem1 (y_g cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_g cx) 72 i HH Gin Hi)). }
assert (LDoff : y_ld cx + 2 * lp + 2 <= ubs0_D_const_u64_0x0101010101010102 \/
ubs0_D_const_u64_0x0101010101010102 + 8 <= y_ld cx + 2 * lp).
{ apply disj_of_pointwise; [|lia|lia]. intros i Hi Hin.
pose proof LDin as LDin'. apply blocks_In in LDin' as (p & Hp & Hpin).
apply (il_blocks IMG L6 A6 mem1 md6 p _ (2 * lp + i) (proj1 HH) Hpin ltac:(lia)).
rewrite Hp. replace (y_ld cx + (2 * lp + i)) with (ubs0_D_const_u64_0x0101010101010102 + (y_ld cx + 2 * lp + i - ubs0_D_const_u64_0x0101010101010102)) by lia.
apply trodata_in_img. lia. }
assert (Goff : y_g cx + 72 <= ubs0_D_const_u64_0x0101010101010102 \/ ubs0_D_const_u64_0x0101010101010102 + 8 <= y_g cx).
{ apply disj_of_pointwise; [|lia|lia]. intros i Hi Hin.
pose proof Gin as Gin'. apply blocks_In in Gin' as (p & Hp & Hpin).
apply (il_blocks IMG L6 A6 mem1 md6 p _ i (proj1 HH) Hpin ltac:(lia)).
rewrite Hp. replace (y_g cx + i) with (ubs0_D_const_u64_0x0101010101010102 + (y_g cx + i - ubs0_D_const_u64_0x0101010101010102)) by lia.
apply trodata_in_img. lia. }
Local Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (tcx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app tcx_tabs fst snd zz_disj y_tisz y_tmsz y_cap cap] in Hs.
septac HSEP 5%nat 6%nat. rename Hs into Hs56.
assert (HS : st_ok ubs0segs E ss_texit (mkst regs (Z_to_bv 64 TPC_EXIT) mem1 (seg_rom ubs0segs))).
{ unfold ss_texit, tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more mem1 TPC_EXIT true); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HF.
- exact HGA.
- intros _ a Ha. apply (present_writable ubs0_msyms). replace a with (y_g cx + (a - y_g cx)) by lia. apply Pg. lia.
- lia.
- lia.
- lia.
- vm_compute; reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_regw _ E mem1 44 2 (y_ld cx + 2 * lp) HE44); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs0_msyms). apply Pld. exact Ho.
+ unfold region_ok, trodata_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split; [intros o Ho; lia|].
constructor; [|constructor]. intros i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
destruct (trodata_bytes i Hi) as [b Hb]. exists b. rewrite Z.add_0_l. unfold img_byte. split; [exact Hb|].
rewrite (HRO i Hi). exact Hb.
- cbn [all_disjoint app]. unfold extent_disjoint, regw, trodata_region, gen_region.
cbn [r_base r_lo r_hi base_val app]. rewrite HE8, HE44, !unsigned_lit_small by lia.
pose proof (eq_refl : ubs0_D_const_u64_0x0101010101010102 = 0x103f0). repeat split; lia.
- cbn [pairwise_disjoint all_disjoint app]. unfold extent_disjoint, regw, trodata_region.
cbn [r_base r_lo r_hi base_val]. rewrite HE44, !unsigned_lit_small by lia.
pose proof (eq_refl : ubs0_D_const_u64_0x0101010101010102 = 0x103f0). repeat split; lia.
- unfold texit_facts. cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE44, !unsigned_lit_small by lia. change (2 ^ 1) with 2. repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
- unfold texit_conds. cbn [conds_ok]. split; [|exact I]. apply (cond_geu E 44 0 37 0 (y_ld cx + 2 * lp) (y_ld cx) HE44 HE37); lia.
- unfold texit_alias. cbn [alias_ok]. split; [|exact I].
apply (alias_b2i' E 37 41 44 (y_ld cx) lp HE37 HE41 HE44); lia. }
clear HE0.
change mem1 with (ms_mem (mkst regs (Z_to_bv 64 TPC_EXIT) mem1 (seg_rom ubs0segs))) in HJ.
assert (LDsep : forall b m, In (b, m) B0 -> y_ld cx + 2 * (y_nP cx + 2 + y_MR cx) <= b \/ b + m <= y_ld cx).
{ intros b m Hbm.
pose proof (heap_sep_perm _ _ LAWS _ _ _ _ (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) _ (b, m) HH
ltac:(eapply Permutation_trans; [exact HB | change (tcx_tabs cx ++ B0) with ([(y_ti cx, 2 * y_idl cx * y_idl cx); (y_lm cx, 8192); (y_lc cx, 4096); (y_li cx, 8192); (y_tm cx, 4098 * y_idl cx)] ++ (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) :: ((y_g cx, 72) :: B0)); apply Permutation_sym; apply Permutation_middle])
ltac:(apply in_app_iff; right; right; exact Hbm)) as Hs. cbn [fst snd] in Hs. exact Hs. }
assert (Gsep : forall b m, In (b, m) B0 -> y_g cx + 72 <= b \/ b + m <= y_g cx).
{ intros b m Hbm.
pose proof (heap_sep_perm _ _ LAWS _ _ _ _ (y_g cx, 72) _ (b, m) HH
ltac:(eapply Permutation_trans; [exact HB | change (tcx_tabs cx ++ B0) with ([(y_ti cx, 2 * y_idl cx * y_idl cx); (y_lm cx, 8192); (y_lc cx, 4096); (y_li cx, 8192); (y_tm cx, 4098 * y_idl cx); (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx))] ++ (y_g cx, 72) :: B0); apply Permutation_sym; apply Permutation_middle])
ltac:(apply in_app_iff; right; exact Hbm)) as Hs. cbn [fst snd] in Hs. exact Hs. }
assert (B0rng : forall b m i, In (b, m) B0 -> 0 <= i < m -> 4096 <= b /\ b + m <= alloc_ceiling).
{ intros b m i Hbm Hi. destruct (heap_blocks _ _ LAWS _ _ _ _ b m i HH ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; right; exact Hbm]) Hi) as (_ & H1 & H2 & _). lia. }
assert (MHI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (y_sp cx - 8192 <= a < y_sp cx) ->
mbyte ubs0segs (ms_mem (mkst regs (Z_to_bv 64 TPC_EXIT) mem1 (seg_rom ubs0segs))) a = mbyte ubs0segs mem1 a)
by (intros; reflexivity).
assert (MBL : forall b m i, In (b, m) B0 -> 0 <= i < m ->
mbyte ubs0segs (ms_mem (mkst regs (Z_to_bv 64 TPC_EXIT) mem1 (seg_rom ubs0segs))) (b + i) = mbyte ubs0segs mem1 (b + i))
by (intros; reflexivity).
assert (MG : forall i, 0 <= i < 48 ->
mbyte ubs0segs (ms_mem (mkst regs (Z_to_bv 64 TPC_EXIT) mem1 (seg_rom ubs0segs))) (y_g cx + i) = mbyte ubs0segs mem1 (y_g cx + i))
by (intros; reflexivity).
assert (HBn : Permutation (blocks L6 A6) (nz [] ++ (tcx_tabs cx ++ B0))) by (cbn [nz List.filter app]; exact HB).
clear HB. rename HBn into HB.
assert (Htok : forall b, In b (nz []) -> wtok' STK sp0 FP (blocks L A) b /\ fst b <> 0) by (intros b Hb; destruct Hb).
Ltac fold_frame cx MHI MBL MG HE2u HE8 HE18 HE44 LDsep Gsep B0rng Hs56 :=
lazymatch goal with HF : frame_of ?E1 ?rs ?m ?m' |- _ =>
let MHI2 := fresh "MHI" in let MBL2 := fresh "MBL" in let MG2 := fresh "MG" in
lazymatch type of MHI with forall a, _ -> _ -> _ = mbyte _ ?m0 a =>
lazymatch type of MBL with forall b mm i, In (b, mm) ?Bf -> _ =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (y_sp cx - 8192 <= a < y_sp cx) ->
mbyte ubs0segs m' a = mbyte ubs0segs m0 a)
by (intros a Ha Hna; rewrite <- (MHI a Ha Hna); apply tmbyte_eq_of1; apply HF;
rewrite unsigned_lit_small by lia;
intros (r0 & Hr0 & Hin0); cbv [In] in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]);
rewrite ?HE2u, ?HE8, ?HE18, ?HE44, ?unsigned_lit_small in Hin0 by lia; lia |]);
destruct Hr0);
assert (MBL2 : forall b mm i, In (b, mm) Bf -> 0 <= i < mm -> mbyte ubs0segs m' (b + i) = mbyte ubs0segs m0 (b + i))
by (intros b mm i Hb Hi; rewrite <- (MBL b mm i Hb Hi); apply tmbyte_eq_of1; apply HF;
pose proof (B0rng b mm i Hb Hi) as [Hb0 Hb1]; pose proof (LDsep b mm Hb) as Hbs; pose proof (Gsep b mm Hb) as Hbg;
rewrite unsigned_lit_small by lia;
intros (r0 & Hr0 & Hin0); cbv [In] in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]);
rewrite ?HE2u, ?HE8, ?HE18, ?HE44, ?unsigned_lit_small in Hin0 by lia; lia |]);
destruct Hr0);
assert (MG2 : forall i, 0 <= i < 48 -> mbyte ubs0segs m' (y_g cx + i) = mbyte ubs0segs m0 (y_g cx + i))
by (intros i Hi; rewrite <- (MG i Hi); apply tmbyte_eq_of1; apply HF;
rewrite unsigned_lit_small by lia;
intros (r0 & Hr0 & Hin0); cbv [In] in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]);
rewrite ?HE2u, ?HE8, ?HE18, ?HE44, ?unsigned_lit_small in Hin0 by lia; lia |]);
destruct Hr0);
clear MHI MBL MG HF; rename MHI2 into MHI; rename MBL2 into MBL; rename MG2 into MG
end end end.
Ltac reg_U HS r v Utac H :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_reg segs E1 ss1 ms1 r HS) as H; eval_sr_get_in H;
rewrite denot_lit_U in H;
lazymatch type of H with _ = Z_to_bv 64 (U ?E2 ?e) =>
let Hv := fresh "Hv" in
assert (Hv : U E2 e = v) by Utac; rewrite Hv in H; clear Hv end end.
Ltac mem_call cx MHI MBL MG HB Hkeep Hhi mem2 lo_tac :=
let MHI2 := fresh "MHI" in let MBL2 := fresh "MBL" in let MG2 := fresh "MG" in
lazymatch type of MHI with forall a, _ -> _ -> _ = mbyte _ ?m1 a =>
lazymatch type of MBL with forall b m i, In (b, m) ?Bf -> _ =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (y_sp cx - 8192 <= a < y_sp cx) ->
mbyte ubs0segs mem2 a = mbyte ubs0segs m1 a)
by (intros a Ha Hna; rewrite (proj1 (Hhi a Ha ltac:(clear - Ha Hna; lo_tac; lia))); exact (MHI a Ha Hna));
assert (MBL2 : forall b m i, In (b, m) Bf -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs m1 (b + i))
by (intros b m i Hb Hi; rewrite (Hkeep b m i ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; right; apply in_app_iff; right; exact Hb]) Hi);
exact (MBL b m i Hb Hi));
assert (MG2 : forall i, 0 <= i < 48 -> mbyte ubs0segs mem2 (y_g cx + i) = mbyte ubs0segs m1 (y_g cx + i))
by (intros i Hi; rewrite (Hkeep (y_g cx) 72 i ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; right; apply in_app_iff; left; inl]) ltac:(lia));
exact (MG i Hi))
end end;
try (lazymatch goal with VK : arr16 _ _ (y_ld cx) ?ll |- _ =>
let V2 := fresh "VK" in
assert (V2 : arr16 ubs0segs mem2 (y_ld cx) ll)
by (eapply arr16_frame; [exact VK|]; intros a Ha; rewrite ?length_app in Ha; cbn [length] in Ha;
replace a with (y_ld cx + (a - y_ld cx)) by lia;
apply (Hkeep (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx)) (a - y_ld cx));
[ eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; right; apply in_app_iff; left; cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; inl'] | lia ]);
clear VK; rename V2 into VLDK end);
clear MHI MBL MG Hkeep; rename MHI2 into MHI; rename MBL2 into MBL; rename MG2 into MG.
Ltac do_malloc cx HS HJ Hid nsz Utac k MHI MBL MG HB Htok HE2u Hspm Htp0 HE :=
let M10 := fresh "M10" in let M2 := fresh "M2" in let M4 := fresh "M4" in let M1 := fresh "M1" in
reg_U HS (10%bv:reg) nsz Utac M10;
(jreg HS (2%bv:reg) as M2); (jreg HS (4%bv:reg) as M4); (jreg HS (1%bv:reg) as M1);
eapply SR_bind;
[ eapply (jmalloc_at _ _ LAWS ubs0_errno_low_lzw IMG (aa_malloc API)) with (n := nsz) (spc := _);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact M10 | lia
| rewrite M2, <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2u; reflexivity | lia | exact Hspm | lia | lia
| rewrite M4, (HE 4%nat (4%bv:reg) eq_refl); exact Htp0
| exact M1 | apply ret_ok_even; vm_compute; reflexivity ]
| ];
clear M10 M2 M4 M1;
let L2 := fresh "L" in let A2 := fresh "A" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in let md2 := fresh "md" in
let res := fresh "res" in
let HJ2 := fresh "HJ" in let Hid2 := fresh "Hid" in let HP2 := fresh "HP" in let Hr10 := fresh "Hr10" in let Hres := fresh "Hres" in
let Hkeep := fresh "Hkeep" in let Hhi := fresh "Hhi" in
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hr10 & Hres & Hkeep & Hhi);
clear HJ Hid; change (ms_segs ubs0_msyms) with ubs0segs in Hkeep, Hhi;
mem_call cx MHI MBL MG HB Hkeep Hhi mem2 ltac:(unfold ALLOC_STACK);
let HB2 := fresh "HB" in
pose proof (tblocks_after_malloc res nsz _ _ _ (blocks L2 A2) HB ltac:(clear - Hres; destruct Hres as [[Hz Hb0]|(Hnz & _ & Hex & _)]; [left; split; [exact Hz | exact Hb0] | right; split; [exact Hnz | exact Hex]])) as HB2;
let Htok2 := fresh "Htok" in
lazymatch type of HB2 with Permutation _ (nz ?cur ++ _) =>
lazymatch type of Htok with forall b, In b _ -> ?W b /\ _ =>
assert (Htok2 : forall b, In b (nz cur) -> W b /\ fst b <> 0)
by (let b := fresh "b" in let Hb := fresh "Hb" in
intros b Hb; destruct (tnz_cases_front b res nsz _ Hb) as [[Hbe Hnz]|Hb'];
[ subst b; split; [| exact Hnz]; destruct Hres as [[Hz _]|(_ & _ & _ & Hw)]; [exfalso; exact (Hnz Hz)|]; exact Hw
| exact (Htok b Hb') ])
end end;
clear HB Htok; rename HB2 into HB; rename Htok2 into Htok;
let HS2 := fresh "HS" in
jafter_call_keep HS k regs2 mem2 HP2 (@nil nat) HS2;
specialize (HS2 ltac:(constructor)); clear HS Hhi HP2; rename HS2 into HS;
let Ha := fresh "Hatom" in
(jreg HS (10%bv:reg) as Ha); cbn [ms_regs mkst] in Ha; rewrite Hr10 in Ha; symmetry in Ha;
rename HJ2 into HJ; rename Hid2 into Hid.
Ltac res_fact HS HJ HB k res nsz Hatom Hnz :=
let R := fresh "R" in
pose proof (heap_blocks_range _ _ LAWS _ _ _ _ res nsz (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; left; apply (proj2 (In_nz _ _)); split; [cbv [app In]; inl' | exact Hnz]]) ltac:(lia)) as R;
add_fact' HS k (mkAF 4096 CEIL_MAX 4); [| ew_havoc; rewrite Hatom, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia].
pose proof (HWT (y_g cx, 72) ltac:(inl)) as Wg.
pose proof (HWT (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) ltac:(cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; inl')) as Wld.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc.
{ wr_norm.
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 8); [reflexivity | rewrite HE8; apply unsigned_lit_small; lia | |].
{ cbn [r_wlo r_whi gen_region]. intros a Ha. eapply (wr_byte_of_wtok _ _ _ _ _ (y_g cx) 72); [exact Wg | exact Gin | lia]. }
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 44); [reflexivity | rewrite HE44; apply unsigned_lit_small; lia | |].
{ cbn [r_wlo r_whi regw]. intros a Ha. eapply (wr_byte_of_wtok _ _ _ _ _ (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx))); [exact Wld | exact LDin | lia]. }
wr_ok_tac. }
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 => lazymatch goal with HFr : frame_of _ _ _ (ms_mem ms1) |- _ =>
assert (VLDK : arr16 ubs0segs (ms_mem ms1) (y_ld cx) (LD ++ [y_idl cx + 1]))
by (eapply arr16_app1; [exact ALD | | lia |];
[ rewrite LenLD; replace (y_ld cx + 2 * lp) with (y_ld cx + 2 * lp + 0) by lia; change 2%nat with (N.to_nat 2);
eapply (tval_mem_of_chunk E1 _ _ 44%nat (y_ld cx + 2 * lp) 0 2%N); [eapply (tst_ok_region_nth _ _ _ 1 _ HS); reflexivity | reflexivity | cbv; tauto
| ew_havoc; rewrite HE44; apply unsigned_lit_small; lia | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; ew_havoc; rewrite HE20, unsigned_lit_small by lia; f_equal; lia
| rewrite LenLD; intros a Ha; apply tmbyte_eq_of1; apply HFr; rewrite unsigned_lit_small by lia;
intros (r0 & Hr0 & Hin0); cbv [In] in Hr0;
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]);
rewrite ?HE2u, ?HE8, ?HE18, ?HE44, ?unsigned_lit_small in Hin0 by lia; lia |]);
destruct Hr0 ]) end end.
clear ALD.
fold_frame cx MHI MBL MG HE2u HE8 HE18 HE44 LDsep Gsep B0rng Hs56.
assert (Hq8v : U E (SAlu ALU_ADD (SAluw ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff 41%nat 0) (SLit 12)) (SLit 12)) (SLit 3)) (SLit 3)) = q8 + 3).
{ etransitivity; [apply (U_bl _ 41 lp); [exact HE41 | exact Hlp0 | lia] | rewrite (hideP_e _ Hq8); reflexivity]. }
do_malloc cx HS HJ Hid (q8 + 3) ltac:(ew_havoc; exact Hq8v) 45%nat MHI MBL MG HB Htok HE2u Hspm Htp0 HE.
rename Hres into Hres1. rename Hatom into Ha1. rename Hr10 into Hr1. rename res into res1.
Ltac fold_ro cx MHI MBL MG :=
lazymatch goal with HF : frame_of _ _ ?m ?m' |- _ =>
let Hro := fresh "Hro" in
pose proof (tframe_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hro; clear HF;
let MHI2 := fresh "MHI" in let MBL2 := fresh "MBL" in let MG2 := fresh "MG" in
lazymatch type of MHI with forall a, _ -> _ -> _ = mbyte _ ?m0 a =>
lazymatch type of MBL with forall b mm i, In (b, mm) ?Bf -> _ =>
assert (MHI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (y_sp cx - 8192 <= a < y_sp cx) ->
mbyte ubs0segs m' a = mbyte ubs0segs m0 a)
by (intros a Ha Hna; rewrite (tmbyte_eq_of1 _ _ a (Hro _)); exact (MHI a Ha Hna));
assert (MBL2 : forall b mm i, In (b, mm) Bf -> 0 <= i < mm -> mbyte ubs0segs m' (b + i) = mbyte ubs0segs m0 (b + i))
by (intros b mm i Hb Hi; rewrite (tmbyte_eq_of1 _ _ (b + i) (Hro _)); exact (MBL b mm i Hb Hi));
assert (MG2 : forall i, 0 <= i < 48 -> mbyte ubs0segs m' (y_g cx + i) = mbyte ubs0segs m0 (y_g cx + i))
by (intros i Hi; rewrite (tmbyte_eq_of1 _ _ (y_g cx + i) (Hro _)); exact (MG i Hi));
try (lazymatch goal with VK : arr16 _ _ (y_ld cx) ?ll |- _ =>
let V2 := fresh "VK" in
assert (V2 : arr16 ubs0segs m' (y_ld cx) ll) by (eapply arr16_frame; [exact VK|]; intros a Ha; exact (tmbyte_eq_of1 _ _ a (Hro _)));
clear VK; rename V2 into VLDK end);
clear MHI MBL MG Hro; rename MHI2 into MHI; rename MBL2 into MBL; rename MG2 into MG
end end end.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc; [wr_ok_tac|]. fold_ro cx MHI MBL MG.
assert (Hq255v : forall E', ew E' 41 = Z_to_bv 64 lp ->
U E' (SAlu ALU_ADD (SMd M_MULHU (SAlu ALU_ADD (SMd M_MUL (SOff 41%nat 0) (SLit 384)) (SLit 384)) (SLit MAGIC_0101)) (SLit 4)) = q255 + 4).
{ intros E' HE'. etransitivity; [apply (U_bb _ 41 lp); [exact HE' | exact Hlp0 | lia] | rewrite (hideP_e _ Hq255); reflexivity]. }
do_malloc cx HS HJ Hid (q255 + 4) ltac:(rewrite U_add0; apply Hq255v; ew_havoc; exact HE41) 61%nat MHI MBL MG HB Htok HE2u Hspm Htp0 HE.
rename Hres into Hres2. rename Hatom into Ha2. rename Hr10 into Hr2. rename res into res2.
jrun_to LAWS ubs0tbl_ok HS HJ TPC_EPIB; [wr_ok_tac|]. fold_ro cx MHI MBL MG.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret. unfold tepi_midV.
rewrite <- (hideP_e _ Hq8), <- (hideP_e _ Hq255).
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lf ?Af _ ?mdf =>
lazymatch goal with |- context [mkst (ms_regs ?msf) _ (ms_mem _) _] =>
exists Lf, Af, (ms_regs msf), (ms_mem msf), mdf, res1, res2 end end.
cbv zeta.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hid|].
Ltac gregm HS rr Hx :=
let Q := fresh "Q" in
(jreg HS rr as Q); cbn [ms_regs mkst] in Q; rewrite Q; clear Q;
first [exact Hx | reflexivity | rewrite Hx; reflexivity | rewrite Hx; rewrite unsigned_lit_small by lia; reflexivity | rewrite Hx].
split; [gregm HS (2%bv:reg) HE2|]. split; [gregm HS (3%bv:reg) (HE 3%nat (3%bv:reg) eq_refl)|]. split; [gregm HS (4%bv:reg) (HE 4%nat (4%bv:reg) eq_refl)|].
split; [gregm HS (8%bv:reg) HE8|]. split; [gregm HS (9%bv:reg) (HE 9%nat (9%bv:reg) eq_refl); exact G9|].
split; [gregm HS (18%bv:reg) HE18|]. split; [gregm HS (19%bv:reg) HE19|]. split; [gregm HS (20%bv:reg) HE20|]. split; [gregm HS (21%bv:reg) Ha2|].
split; [gregm HS (22%bv:reg) HE41|]. split; [gregm HS (23%bv:reg) Ha1|].
cbn [ms_mem mkst].
split.
{ destruct HGA as (_ & _ & _ & _ & _ & V40 & _). intros k Hk. rewrite <- Z.add_assoc. rewrite (MG (40 + Z.of_nat k)) by (cbn in Hk; lia).
rewrite Z.add_assoc. apply V40. exact Hk. }
split; [exact MHI|]. split; [exact MBL|]. split; [exact MG|]. split; [exact HB|]. split; [exact Htok|].
split.
{ intros Hnz1. destruct Hres1 as [[Hz _] | (_ & Hal1 & _ & _)]; [exfalso; exact (Hnz1 Hz)|].
pose proof (heap_blocks_range _ _ LAWS _ _ _ _ res1 (q8 + 3) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; left; apply (proj2 (In_nz _ _)); split; [cbv [app In]; inl' | exact Hnz1]]) ltac:(lia)) as R. lia. }
split; [| exact VLDK].
intros Hnz2. destruct Hres2 as [[Hz _] | (_ & Hal2 & _ & _)]; [exfalso; exact (Hnz2 Hz)|].
pose proof (heap_blocks_range _ _ LAWS _ _ _ _ res2 (q255 + 4) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; left; apply (proj2 (In_nz _ _)); split; [cbv [app In]; inl' | exact Hnz2]]) ltac:(lia)) as R. lia.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
