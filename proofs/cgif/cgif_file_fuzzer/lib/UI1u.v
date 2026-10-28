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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 UIZ6.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ubs0_errno_low_cbl : errno_addr ubs0_msyms + 4 <= alloc_ceiling.
Proof using.   pose proof (proj1 alloc_ceiling_val). enough (errno_addr ubs0_msyms + 4 <= CEIL_MIN) by lia. vm_compute. intros H'. discriminate H'. Qed.
Definition ss_A : sstate := mkSS (ubs0_A_create_byte_list + UOFF_A) sr_cblu [] None (mkFacts cblu_facts_A [] []).
Definition ss_B : sstate := mkSS (ubs0_A_create_byte_list + UOFF_B) sr_cblu [R9; R32] None (mkFacts cblu_facts_B cblu_cond cbl_alias).
Definition ss_C : sstate := mkSS (ubs0_A_create_byte_list + UOFF_C) sr_cblu [R9] None (mkFacts cblu_facts_C [] []).
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma atoms_ok_core : forall regs extra L A mem md bl Lby lz Llz lzwPos D C0 i bp Lc,
heap_ok MR L A mem md -> In (bl, Lby) (blocks L A) -> In (lz, Llz) (blocks L A) ->
cbl_regs_fix_u regs bl lz D C0 -> cbl_fix Lby Llz lzwPos D C0 ->
getr regs 8 = Z_to_bv 64 (lz + 2 * i) -> getr regs 9 = Z_to_bv 64 (lz + 2 * i) -> getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
getr regs 15 = Z_to_bv 64 bp -> getr regs 18 = Z_to_bv 64 Lc ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> 0 <= Lc <= 12 -> 0 < Lby ->
atoms_ok (Ereg regs extra) cblu_facts_core.
Proof using LAWS.
intros regs extra L A mem md bl Lby lz Llz lzwPos D C0 i bp Lc HH Hbl Hlz
(H10 & H12 & H13 & H14 & H16 & H5 & H17 & H6 & H7 & H28 & H31 & H30) (F1 & F2 & F3 & F4 & F5) H8 H9 H29 H15 H18 Hi Hbp HLc HLby.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md bl Lby HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md lz Llz HH Hlz ltac:(lia)) as (Bz0 & Bz1 & Bz16).
cbn [atoms_ok cblu_facts_core]. unfold afact_ok, NOTBL. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 10 10%bv), (ew_Ereg_nat regs _ 12 12%bv), (ew_Ereg_nat regs _ 5 5%bv),
(ew_Ereg_nat regs _ 8 8%bv), (ew_Ereg_nat regs _ 9 9%bv), (ew_Ereg_nat regs _ 29 29%bv),
(ew_Ereg_nat regs _ 13 13%bv), (ew_Ereg_nat regs _ 14 14%bv), (ew_Ereg_nat regs _ 16 16%bv),
(ew_Ereg_nat regs _ 15 15%bv), (ew_Ereg_nat regs _ 18 18%bv) by (vm_compute; reflexivity).
rewrite H10, H12, H5, H8, H9, H29, H13, H14, H16, H15, H18, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; first [exact Bl16 | lia].
Qed.
Lemma R9_ok : forall regs L A mem md lz Llz i (w1 : word),
heap_ok MR L A mem md -> In (lz, Llz) (blocks L A) ->
getr regs 9 = Z_to_bv 64 (lz + 2 * i) -> 0 <= i -> 2 * i + 2 <= Llz ->
exists X, 0 <= X < 2 ^ 16 /\
forall extra, region_ok ubs0segs (Ereg regs (w1 :: Z_to_bv 64 X :: extra)) mem R9.
Proof using LAWS.
intros regs L A mem md lz Llz i w1 HH Hlz H9 Hi HiL.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md lz Llz HH Hlz ltac:(lia)) as (Bz0 & Bz1 & Bz16).
destruct (val_mem2 ubs0segs mem (lz + 2 * i)) as (X & HX & HV).
{ apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ lz Llz (2 * i) HH Hlz ltac:(lia))). }
{ replace (lz + 2 * i + 1) with (lz + (2 * i + 1)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ lz Llz (2 * i + 1) HH Hlz ltac:(lia))). }
exists X. split; [exact HX|]. intros extra.
unfold region_ok, R9. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite (ew_Ereg_nat regs _ 9 9%bv) by (vm_compute; reflexivity). rewrite H9, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply chunk_ok_val; [| exact HX | cbn; lia | rewrite Z.add_0_r; exact HV].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 1). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma R32_ok : forall regs L A mem md bl Lby bp w2,
heap_ok MR L A mem md -> In (bl, Lby) (blocks L A) ->
0 <= bp -> bp + 3 <= Lby ->
exists Y0 Y1 Y2, 0 <= Y0 < 256 /\ 0 <= Y1 < 256 /\ 0 <= Y2 < 256 /\
forall extra, region_ok ubs0segs (Ereg regs (Z_to_bv 64 (bl + bp) :: w2 :: Z_to_bv 64 Y0 :: Z_to_bv 64 Y1 :: Z_to_bv 64 Y2 :: extra)) mem R32.
Proof using LAWS.
intros regs L A mem md bl Lby bp w2 HH Hbl Hbp HbpL.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md bl Lby HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
assert (HP : forall j, 0 <= j < 3 -> present mem (bl + bp + j)).
{ intros j Hj. replace (bl + bp + j) with (bl + (bp + j)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bl Lby (bp + j) HH Hbl ltac:(lia))). }
destruct (val_mem1 ubs0segs mem (bl + bp)) as (Y0 & HY0 & HV0); [replace (bl + bp) with (bl + bp + 0) by lia; apply HP; lia|].
destruct (val_mem1 ubs0segs mem (bl + bp + 1)) as (Y1 & HY1 & HV1); [apply HP; lia|].
destruct (val_mem1 ubs0segs mem (bl + bp + 2)) as (Y2 & HY2 & HV2); [apply HP; lia|].
exists Y0, Y1, Y2. split; [exact HY0|]. split; [exact HY1|]. split; [exact HY2|]. intros extra.
unfold region_ok, R32. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite (ew_Ereg_extra regs _ 0). cbn [nth]. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs0_msyms). apply HP. lia. }
constructor; [|constructor; [|constructor; [|constructor]]].
- eapply chunk_ok_val; [| exact HY0 | cbn; lia | rewrite Z.add_0_r; exact HV0].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 2). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- eapply chunk_ok_val; [| exact HY1 | cbn; lia | exact HV1].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 3). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- eapply chunk_ok_val; [| exact HY2 | cbn; lia | exact HV2].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 4). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma cbl_segA : forall regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b Lc,
journal ubs0_msyms MR STK sp0 FP L A mem md L A memc md ->
In (bl, Lby) (blocks L A) -> In (lz, Llz) (blocks L A) ->
cbl_regs_fix_u regs bl lz D C0 -> cbl_fix Lby Llz lzwPos D C0 ->
getr regs 8 = Z_to_bv 64 (lz + 2 * i) -> getr regs 9 = Z_to_bv 64 (lz + 2 * i) -> getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
getr regs 15 = Z_to_bv 64 bp -> getr regs 20 = Z_to_bv 64 b -> getr regs 18 = Z_to_bv 64 Lc ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> bp + 3 <= Lby -> 0 <= b <= 7 -> 0 <= Lc <= 12 ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 (ubs0_A_create_byte_list + UOFF_A)) memc (seg_rom ubs0segs)) md)
(fun c' => exists regs' mem' L',
c' = mkCfg (mkst regs' (Z_to_bv 64 (ubs0_A_create_byte_list + UOFF_B)) mem' (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR STK sp0 FP L A mem md L A mem' md /\
(forall x, mem' x = memc x) /\
cbl_regs_fix_u regs' bl lz D C0 /\
getr regs' 8 = Z_to_bv 64 (lz + 2 * i) /\ getr regs' 9 = Z_to_bv 64 (lz + 2 * i) /\
getr regs' 29 = Z_to_bv 64 (lzwPos - i) /\ getr regs' 15 = Z_to_bv 64 bp /\ getr regs' 20 = Z_to_bv 64 b /\
getr regs' 18 = Z_to_bv 64 L' /\ 0 <= L' <= 12 /\
(forall r, In r KEPTU -> getr regs' r = getr regs r)).
Proof using IMG LAWS.
intros regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b Lc
HJ Hbl Hlz Hfix Hcf H8 H9 H29 H15 H20 H18 Hi Hbp HbpL Hb HLc.
pose proof Hfix as (H10 & H12 & H13 & H14 & H16 & H5 & H17 & H6 & H7 & H28 & H31 & H30).
pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HH.
remember (Ereg regs []) as E eqn:HE.
assert (HA : env_agree 32 (Ereg regs []) E) by (rewrite HE; apply env_agree_refl).
assert (HE18 : ew E 18 = Z_to_bv 64 Lc) by (rewrite HE, (ew_Ereg_nat regs _ 18 18%bv) by (vm_compute; reflexivity); exact H18).
assert (HE20 : ew E 20 = Z_to_bv 64 b) by (rewrite HE, (ew_Ereg_nat regs _ 20 20%bv) by (vm_compute; reflexivity); exact H20).
set (ms0 := mkst regs (Z_to_bv 64 (ubs0_A_create_byte_list + UOFF_A)) memc (seg_rom ubs0segs)).
assert (HS : st_ok ubs0segs E ss_A ms0).
{ rewrite HE. apply entry_st_ok_any.
- apply regs_ok_cblu; assumption.
- reflexivity.
- constructor.
- exact I.
- split; [|split; exact I]. unfold ss_A, cblu_facts_A. cbn [f_atoms]. apply atoms_ok_app.
+ eapply (atoms_ok_core regs _ L A memc md bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 20 20%bv) by (vm_compute; reflexivity).
rewrite H20, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia. }
change memc with (ms_mem ms0) in HJ.
Local Ltac leafA HS HJ HA HE18 Hfix :=
lazymatch type of HE18 with ew ?E 18 = Z_to_bv 64 ?Lc =>
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok _ _ _ _ _ _ (KEPTU ++ [10; 12; 13; 14; 16; 5; 8; 9; 29; 15; 20]%bv) HS HA ltac:(vm_compute; reflexivity)) as HK;
let Q17 := fresh "Q17" in let Q6 := fresh "Q6" in let Q7 := fresh "Q7" in
let Q28 := fresh "Q28" in let Q31 := fresh "Q31" in let Q30 := fresh "Q30" in let Q18 := fresh "Q18" in
jreg HS (17%bv:reg) as Q17; jreg HS (6%bv:reg) as Q6; jreg HS (7%bv:reg) as Q7;
jreg HS (28%bv:reg) as Q28; jreg HS (31%bv:reg) as Q31; jreg HS (30%bv:reg) as Q30; jreg HS (18%bv:reg) as Q18;
rewrite HE18 in Q18; rewrite ?unsigned_lit_small in Q18 by lia;
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch type of Q18 with getr _ _ = Z_to_bv 64 ?L' =>
lazymatch type of HS with st_ok _ _ _ ?msx =>
exists (ms_regs msx), (ms_mem msx), L' end end;
split; [reflexivity|]; split; [exact HJ|];
split; [ intros x;
repeat lazymatch goal with HF : frame_of _ [] _ _ |- _ => rewrite (frame_of_nil _ _ _ x HF); clear HF end;
reflexivity |];
destruct Hfix as (?H10 & ?H12 & ?H13 & ?H14 & ?H16 & ?H5 & _ & _ & _ & _ & _ & _);
split; [ unfold cbl_regs_fix_u; repeat split; first [kreg HK | exact Q17 | exact Q6 | exact Q7 | exact Q28 | exact Q31 | exact Q30] |];
split; [kreg HK|]; split; [kreg HK|]; split; [kreg HK|]; split; [kreg HK|]; split; [kreg HK|];
split; [exact Q18|]; split; [lia|];
intros r Hr; apply HK; apply in_app_iff; left; exact Hr
end.
jrun_to LAWS ubs0tbl_ok HS HJ (ubs0_A_create_byte_list + UOFF_B). { apply wr_ok_nil. }
jbranch ubs0tbl HS.
-
jrun_to LAWS ubs0tbl_ok HS HJ (ubs0_A_create_byte_list + UOFF_B). { apply wr_ok_nil. }
leafA HS HJ HA HE18 Hfix.
- cnormu Hc HE18 HE20.
jrun_to LAWS ubs0tbl_ok HS HJ (ubs0_A_create_byte_list + UOFF_B). { apply wr_ok_nil. }
jbranch ubs0tbl HS.
+ jrun_to LAWS ubs0tbl_ok HS HJ (ubs0_A_create_byte_list + UOFF_B). { apply wr_ok_nil. }
leafA HS HJ HA HE18 Hfix.
+ jrun_to LAWS ubs0tbl_ok HS HJ (ubs0_A_create_byte_list + UOFF_B). { apply wr_ok_nil. }
leafA HS HJ HA HE18 Hfix.
Qed.
Lemma cbl_segB : forall regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b Lc,
journal ubs0_msyms MR STK sp0 FP L A mem md L A memc md ->
In (bl, Lby) (blocks L A) -> In (lz, Llz) (blocks L A) -> (bl + Lby <= lz \/ lz + Llz <= bl) ->
(forall a, bl <= a < bl + Lby -> inFP FP a) ->
cbl_regs_fix_u regs bl lz D C0 -> cbl_fix Lby Llz lzwPos D C0 ->
getr regs 8 = Z_to_bv 64 (lz + 2 * i) -> getr regs 9 = Z_to_bv 64 (lz + 2 * i) -> getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
getr regs 15 = Z_to_bv 64 bp -> getr regs 20 = Z_to_bv 64 b -> getr regs 18 = Z_to_bv 64 Lc ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> bp + 3 <= Lby -> 0 <= b <= 7 -> 0 <= Lc <= 12 ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 (ubs0_A_create_byte_list + UOFF_B)) memc (seg_rom ubs0segs)) md)
(fun c' => exists regs' mem' s corr,
c' = mkCfg (mkst regs' (Z_to_bv 64 (ubs0_A_create_byte_list + UOFF_C)) mem' (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR STK sp0 FP L A mem md L A mem' md /\
(forall x : word, bv_unsigned x < bl + bp \/ bl + bp + 3 <= bv_unsigned x -> mem' x = memc x) /\
mem_grows memc mem' /\
cbl_regs_fix_u regs' bl lz D C0 /\
getr regs' 8 = Z_to_bv 64 (lz + 2 * i) /\ getr regs' 9 = Z_to_bv 64 (lz + 2 * i) /\
getr regs' 29 = Z_to_bv 64 (lzwPos - i) /\
getr regs' 15 = Z_to_bv 64 (bp + s) /\ getr regs' 18 = Z_to_bv 64 Lc /\
getr regs' 21 = Z_to_bv 64 (b + Lc) /\ getr regs' 22 = Z_to_bv 64 corr /\
(corr = 0 \/ (corr = -1 /\ 1 <= s)) /\ 0 <= s <= 2 /\ 8 * s <= b + Lc < 8 * s + 8 /\
(forall r, In r KEPTU -> getr regs' r = getr regs r)).
Proof using IMG LAWS.
intros regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b Lc
HJ Hbl Hlz Hdisj HFP Hfix Hcf H8 H9 H29 H15 H20 H18 Hi Hbp HbpL Hb HLc.
pose proof Hfix as (H10 & H12 & H13 & H14 & H16 & H5 & H17 & H6 & H7 & H28 & H31 & H30).
pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HH.
destruct (heap_blocks_range ubs0_msyms MR LAWS L A memc md bl Lby HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A memc md lz Llz HH Hlz ltac:(lia)) as (Bz0 & Bz1 & Bz16).
destruct (R9_ok regs L A memc md lz Llz i (Z_to_bv 64 (bl + bp)) HH Hlz H9 ltac:(lia) ltac:(lia)) as (X & HX & HR9).
destruct (R32_ok regs L A memc md bl Lby bp (Z_to_bv 64 X) HH Hbl ltac:(lia) HbpL) as (Y0 & Y1 & Y2 & HY0 & HY1 & HY2 & HR32).
specialize (HR9 [Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2]). specialize (HR32 (@nil word)).
remember (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 X; Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2]) as E eqn:HE.
rename HR32 into HR32'.
assert (HA : env_agree 32 (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 X; Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2]) E)
by (rewrite HE; apply env_agree_refl).
assert (HE18 : ew E 18 = Z_to_bv 64 Lc) by (rewrite HE, (ew_Ereg_nat regs _ 18 18%bv) by (vm_compute; reflexivity); exact H18).
assert (HE20 : ew E 20 = Z_to_bv 64 b) by (rewrite HE, (ew_Ereg_nat regs _ 20 20%bv) by (vm_compute; reflexivity); exact H20).
assert (HE15 : ew E 15 = Z_to_bv 64 bp) by (rewrite HE, (ew_Ereg_nat regs _ 15 15%bv) by (vm_compute; reflexivity); exact H15).
assert (HE10 : ew E 10 = Z_to_bv 64 bl) by (rewrite HE, (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity); exact H10).
assert (HE8 : ew E 8 = Z_to_bv 64 (lz + 2 * i)) by (rewrite HE, (ew_Ereg_nat regs _ 8 8%bv) by (vm_compute; reflexivity); exact H8).
assert (HE9 : ew E 9 = Z_to_bv 64 (lz + 2 * i)) by (rewrite HE, (ew_Ereg_nat regs _ 9 9%bv) by (vm_compute; reflexivity); exact H9).
assert (HE12 : ew E 12 = Z_to_bv 64 lz) by (rewrite HE, (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity); exact H12).
assert (HE32 : ew E 32 = Z_to_bv 64 (bl + bp)) by (rewrite HE, (ew_Ereg_extra regs _ 0); reflexivity).
set (ms0 := mkst regs (Z_to_bv 64 (ubs0_A_create_byte_list + UOFF_B)) memc (seg_rom ubs0segs)).
assert (HS : st_ok ubs0segs E ss_B ms0).
{ apply entry_st_ok_any.
- rewrite HE. apply regs_ok_cblu; assumption.
- vm_compute. reflexivity.
- constructor; [exact HR9 | constructor; [exact HR32' | constructor]].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, R9, R32. cbn [r_base r_lo r_hi base_val].
rewrite HE9, HE32, !unsigned_lit_small by lia. repeat split. lia.
- split; [|split].
+ unfold ss_B, cblu_facts_B. cbn [f_atoms]. apply atoms_ok_app.
* rewrite HE. eapply (atoms_ok_core regs _ L A memc md bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
* cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE20, HE32. rewrite HE, (ew_Ereg_extra regs _ 1), (ew_Ereg_extra regs _ 2), (ew_Ereg_extra regs _ 3), (ew_Ereg_extra regs _ 4).
cbn [nth]. rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia.
+ cbn [f_conds ss_B cblu_cond conds_ok acond_ok ac_c ac_a ac_b]. split; [|exact I].
unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, (U_atom E 8 (lz + 2 * i) HE8), (U_atom E 12 lz HE12) by lia.
apply Bool.negb_true_iff, Z.ltb_ge. lia.
+ cbn [f_alias ss_B cbl_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 10 bl HE10), (U_atom E 15 bp HE15), (U_atom E 32 (bl + bp) HE32) by lia.
apply zcanon_id. unfold M64. lia. }
change memc with (ms_mem ms0) in HJ. change memc with (ms_mem ms0). clear Bl16 Bz16.
assert (Hwr : forall E' cs1 cs2, ew E' 32 = Z_to_bv 64 (bl + bp) ->
wr_ok E' [YP09.mkRegion (Some 9%nat) 0 2 0 0 cs1; YP09.mkRegion (Some 32%nat) 0 3 0 3 cs2]
STK sp0 FP (blocks L A) (blocks L A)).
{ intros E' cs1 cs2 HE32'. apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 32 (bl + bp) bl Lby);
[reflexivity | rewrite HE32'; apply unsigned_lit_small; lia | exact Hbl | cbn; lia | cbn; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. apply HFP. lia. }
Local Ltac leafB HS HJ HA HE18 HE20 HE15 HE32 Hfix :=
lazymatch type of HE15 with ew ?E 15 = Z_to_bv 64 ?bp =>
lazymatch type of HE32 with ew _ 32 = Z_to_bv 64 (?bl + _) =>
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok _ _ _ _ _ _ (KEPTU ++ [10; 12; 13; 14; 16; 5; 8; 9; 29; 18]%bv) HS HA ltac:(vm_compute; reflexivity)) as HK;
let Q17 := fresh "Q17" in let Q6 := fresh "Q6" in let Q7 := fresh "Q7" in
let Q28 := fresh "Q28" in let Q31 := fresh "Q31" in let Q30 := fresh "Q30" in
let Q15 := fresh "Q15" in let Q22 := fresh "Q22" in let Q21 := fresh "Q21" in
jreg HS (17%bv:reg) as Q17; jreg HS (6%bv:reg) as Q6; jreg HS (7%bv:reg) as Q7;
jreg HS (28%bv:reg) as Q28; jreg HS (31%bv:reg) as Q31; jreg HS (30%bv:reg) as Q30;
jreg HS (15%bv:reg) as Q15; jreg HS (22%bv:reg) as Q22;
rewrite HE15 in Q15; rewrite ?unsigned_lit_small in Q15 by lia;
lazymatch type of Q15 with _ = Z_to_bv 64 bp => rewrite <- (Z.add_0_r bp) in Q15 | _ => idtac end;
rewrite ?lit_m1 in Q22;
pose proof (st_ok_reg_U _ _ _ _ 21%bv HS) as Q21;
lazymatch type of Q21 with _ = Z_to_bv 64 (U _ (sr_get ?sr ?r)) =>
let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e in Q21 end;
rewrite (U_t6 _ 18 _ _ 20 _ HE18 HE20) in Q21 by lia; rewrite ?Z.add_0_r in Q21;
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch type of HS with st_ok _ _ _ ?msx =>
eexists (ms_regs msx), (ms_mem msx), _, _ end;
split; [reflexivity|]; split; [exact HJ|];
split; [ intros x Hx;
repeat lazymatch goal with HF : frame_of _ (_ :: _) _ ?m2 |- ?m3 x = _ =>
lazymatch m3 with context [m2] =>
rewrite (frame_of_one _ _ _ _ (bl + bp) (bl + bp + 3) x (frame_of_cons_ro _ _ _ _ _ HF ltac:(cbn; lia)));
[ clear HF | cbn [r_base r_wlo r_whi base_val]; ew_havoc; rewrite HE32, unsigned_lit_small by lia; lia
| cbn [r_base r_wlo r_whi base_val]; ew_havoc; rewrite HE32, unsigned_lit_small by lia; lia | exact Hx ] end end;
reflexivity |];
split; [ repeat lazymatch goal with HG : mem_grows _ ?m2 |- mem_grows _ ?m3 =>
first [ exact HG | eapply mem_grows_trans; [|exact HG]; clear HG ] end |];
destruct Hfix as (?H10 & ?H12 & ?H13 & ?H14 & ?H16 & ?H5 & _ & _ & _ & _ & _ & _);
split; [ unfold cbl_regs_fix_u; repeat split; first [kreg HK | exact Q17 | exact Q6 | exact Q7 | exact Q28 | exact Q31 | exact Q30] |];
split; [kreg HK|]; split; [kreg HK|]; split; [kreg HK|];
split; [exact Q15|]; split; [kreg HK|]; split; [exact Q21|]; split; [exact Q22|];
split; [lia|]; split; [lia|]; split; [lia|];
intros r Hr; apply HK; apply in_app_iff; left; exact Hr
end end.
Local Ltac runB LAWS HS HJ Hwr HE32 := jrun_to LAWS ubs0tbl_ok HS HJ (ubs0_A_create_byte_list + UOFF_C); [wr_norm; apply Hwr; ew_havoc; exact HE32|].
runB LAWS HS HJ Hwr HE32.
jbranch ubs0tbl HS; cnormu Hc HE18 HE20; runB LAWS HS HJ Hwr HE32.
-   leafB HS HJ HA HE18 HE20 HE15 HE32 Hfix.
- jbranch ubs0tbl HS; cnormu Hc0 HE18 HE20; runB LAWS HS HJ Hwr HE32.
+   jbranch ubs0tbl HS; cnormu Hc1 HE18 HE20; runB LAWS HS HJ Hwr HE32.
*   jbranch ubs0tbl HS; cnormu Hc2 HE18 HE20; runB LAWS HS HJ Hwr HE32.
--   leafB HS HJ HA HE18 HE20 HE15 HE32 Hfix.
--   leafB HS HJ HA HE18 HE20 HE15 HE32 Hfix.
*   leafB HS HJ HA HE18 HE20 HE15 HE32 Hfix.
+   leafB HS HJ HA HE18 HE20 HE15 HE32 Hfix.
Qed.
Lemma cbl_segC : forall regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp t Lc,
journal ubs0_msyms MR STK sp0 FP L A mem md L A memc md ->
In (bl, Lby) (blocks L A) -> In (lz, Llz) (blocks L A) ->
cbl_regs_fix_u regs bl lz D C0 -> cbl_fix Lby Llz lzwPos D C0 ->
getr regs 8 = Z_to_bv 64 (lz + 2 * i) -> getr regs 9 = Z_to_bv 64 (lz + 2 * i) -> getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
getr regs 15 = Z_to_bv 64 bp -> getr regs 18 = Z_to_bv 64 Lc -> getr regs 21 = Z_to_bv 64 t ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> 0 <= t <= 19 -> 0 <= Lc <= 12 ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 (ubs0_A_create_byte_list + UOFF_C)) memc (seg_rom ubs0segs)) md)
(fun c' => exists regs' mem' b' m L',
c' = mkCfg (mkst regs' (Z_to_bv 64 (ubs0_A_create_byte_list + (if i + 1 =? lzwPos then UOFF_X else UOFF_A))) mem' (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR STK sp0 FP L A mem md L A mem' md /\
(forall x, mem' x = memc x) /\
cbl_regs_fix_u regs' bl lz D C0 /\
getr regs' 8 = Z_to_bv 64 (lz + 2 * (i + 1)) /\ getr regs' 9 = Z_to_bv 64 (lz + 2 * (i + 1)) /\
getr regs' 29 = Z_to_bv 64 (lzwPos - (i + 1)) /\
getr regs' 15 = Z_to_bv 64 bp /\ getr regs' 22 = getr regs 22 /\
getr regs' 20 = Z_to_bv 64 b' /\ getr regs' 18 = Z_to_bv 64 L' /\
t = 8 * m + b' /\ 0 <= b' < 8 /\ 0 <= L' <= 12 /\
(forall r, In r KEPTU -> getr regs' r = getr regs r)).
Proof using IMG LAWS.
intros regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp t Lc
HJ Hbl Hlz Hfix Hcf H8 H9 H29 H15 H18 H21 Hi Hbp Ht HLc.
pose proof Hfix as (H10 & H12 & H13 & H14 & H16 & H5 & H17 & H6 & H7 & H28 & H31 & H30).
pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HH.
destruct (heap_blocks_range ubs0_msyms MR LAWS L A memc md bl Lby HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A memc md lz Llz HH Hlz ltac:(lia)) as (Bz0 & Bz1 & Bz16).
destruct (R9_ok regs L A memc md lz Llz i (Z_to_bv 64 0) HH Hlz H9 ltac:(lia) ltac:(lia)) as (X & HX & HR9).
specialize (HR9 (@nil word)).
remember (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 X]) as E eqn:HE.
assert (HA : env_agree 32 (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 X]) E) by (rewrite HE; apply env_agree_refl).
assert (HE18 : ew E 18 = Z_to_bv 64 Lc) by (rewrite HE, (ew_Ereg_nat regs _ 18 18%bv) by (vm_compute; reflexivity); exact H18).
assert (HE21 : ew E 21 = Z_to_bv 64 t) by (rewrite HE, (ew_Ereg_nat regs _ 21 21%bv) by (vm_compute; reflexivity); exact H21).
assert (HE14 : ew E 14 = Z_to_bv 64 C0) by (rewrite HE, (ew_Ereg_nat regs _ 14 14%bv) by (vm_compute; reflexivity); exact H14).
assert (HE8 : ew E 8 = Z_to_bv 64 (lz + 2 * i)) by (rewrite HE, (ew_Ereg_nat regs _ 8 8%bv) by (vm_compute; reflexivity); exact H8).
assert (HE9 : ew E 9 = Z_to_bv 64 (lz + 2 * i)) by (rewrite HE, (ew_Ereg_nat regs _ 9 9%bv) by (vm_compute; reflexivity); exact H9).
assert (HE29 : ew E 29 = Z_to_bv 64 (lzwPos - i)) by (rewrite HE, (ew_Ereg_nat regs _ 29 29%bv) by (vm_compute; reflexivity); exact H29).
set (ms0 := mkst regs (Z_to_bv 64 (ubs0_A_create_byte_list + UOFF_C)) memc (seg_rom ubs0segs)).
assert (HS : st_ok ubs0segs E ss_C ms0).
{ apply entry_st_ok_any.
- rewrite HE. apply regs_ok_cblu; assumption.
- vm_compute. reflexivity.
- constructor; [exact HR9 | constructor].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I].
unfold ss_C, cblu_facts_C. cbn [f_atoms]. apply atoms_ok_app.
+ rewrite HE. eapply (atoms_ok_core regs _ L A memc md bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE21. rewrite HE, (ew_Ereg_extra regs _ 1). cbn [nth]. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
change memc with (ms_mem ms0) in HJ. change memc with (ms_mem ms0). clear Bl16 Bz16.
Local Ltac leafC HS HJ HA HE18 HE21 HE14 HE8 HE9 HE29 Hfix :=
lazymatch type of HE21 with ew ?E 21 = Z_to_bv 64 ?t =>
lazymatch type of HE8 with ew _ 8 = Z_to_bv 64 (?lz + 2 * ?i) =>
lazymatch type of HE29 with ew _ 29 = Z_to_bv 64 (?lzwPos - _) =>
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok _ _ _ _ _ _ (KEPTU ++ [10; 12; 13; 14; 16; 5; 15; 22]%bv) HS HA ltac:(vm_compute; reflexivity)) as HK;
let Q17 := fresh "Q17" in let Q6 := fresh "Q6" in let Q7 := fresh "Q7" in
let Q28 := fresh "Q28" in let Q31 := fresh "Q31" in let Q30 := fresh "Q30" in
let Q8 := fresh "Q8" in let Q9 := fresh "Q9" in let Q29 := fresh "Q29" in let Q18 := fresh "Q18" in let Q20 := fresh "Q20" in
jreg HS (17%bv:reg) as Q17; jreg HS (6%bv:reg) as Q6; jreg HS (7%bv:reg) as Q7;
jreg HS (28%bv:reg) as Q28; jreg HS (31%bv:reg) as Q31; jreg HS (30%bv:reg) as Q30;
jreg HS (8%bv:reg) as Q8; jreg HS (9%bv:reg) as Q9; jreg HS (29%bv:reg) as Q29; jreg HS (18%bv:reg) as Q18;
rewrite HE8, unsigned_lit_small in Q8 by lia; rewrite HE9, unsigned_lit_small in Q9 by lia;
rewrite HE29, unsigned_lit_small in Q29 by lia;
first [rewrite HE18 in Q18 | rewrite HE14 in Q18];
pose proof (st_ok_reg_U _ _ _ _ 20%bv HS) as Q20;
lazymatch type of Q20 with _ = Z_to_bv 64 (U _ (sr_get ?sr ?r)) =>
let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e in Q20 end;
rewrite U_and_lit in Q20 by lia0; rewrite (U_atom _ 21 t HE21) in Q20 by lia;
let m := fresh "m" in let Hm := fresh "Hm" in
destruct (land7_split t ltac:(lia)) as (m & Hm);
repeat match goal with Hc : branch_taken _ (sv_denot _ (SOff 29 _)) _ = _ |- _ =>
first [rewrite branch_ne_U in Hc | rewrite branch_eq_U in Hc];
rewrite (U_atom_off _ 29 (lzwPos - i) (-1) HE29) in Hc by lia; rewrite ?U_lit in Hc by lia0;
first [ apply (proj1 (Bool.negb_true_iff _)) in Hc | apply (proj1 (Bool.negb_false_iff _)) in Hc | idtac ];
first [ apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc ] end;
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch type of Q18 with _ = Z_to_bv 64 ?L' =>
lazymatch type of HS with st_ok _ _ _ ?msx =>
exists (ms_regs msx), (ms_mem msx), (Z.land t 7), m, L' end end;
split; [ first [ replace (i + 1 =? lzwPos) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity
| replace (i + 1 =? lzwPos) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity ] |];
split; [exact HJ|];
split; [ intros x;
repeat lazymatch goal with HF : frame_of _ (_ :: _) _ ?m2 |- ?m3 x = _ =>
lazymatch m3 with context [m2] =>
rewrite (frame_of_nil _ _ _ x (frame_of_cons_ro _ _ _ _ _ HF ltac:(cbn; lia))); clear HF end end;
reflexivity |];
destruct Hfix as (?H10 & ?H12 & ?H13 & ?H14 & ?H16 & ?H5 & _ & _ & _ & _ & _ & _);
split; [ unfold cbl_regs_fix_u; repeat split; first [kreg HK | exact Q17 | exact Q6 | exact Q7 | exact Q28 | exact Q31 | exact Q30] |];
split; [rewrite Q8; f_equal; lia|]; split; [rewrite Q9; f_equal; lia|]; split; [rewrite Q29; f_equal; lia|];
split; [kreg HK|]; split; [apply HK; cbv; tauto|];
split; [exact Q20|]; split; [exact Q18|];
split; [lia|]; split; [lia|]; split; [lia|];
intros r Hr; apply HK; apply in_app_iff; left; exact Hr
end end end.
Local Ltac runC LAWS HS HJ tgt := jrun_to LAWS ubs0tbl_ok HS HJ (ubs0_A_create_byte_list + tgt); [wr_norm; apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil] |].
runC LAWS HS HJ UOFF_A.
jbranch ubs0tbl HS; runC LAWS HS HJ UOFF_A.
-
jbranch ubs0tbl HS.
+ runC LAWS HS HJ UOFF_A. leafC HS HJ HA HE18 HE21 HE14 HE8 HE9 HE29 Hfix.
+ runC LAWS HS HJ UOFF_X. leafC HS HJ HA HE18 HE21 HE14 HE8 HE9 HE29 Hfix.
-
jbranch ubs0tbl HS.
+ runC LAWS HS HJ UOFF_A. leafC HS HJ HA HE18 HE21 HE14 HE8 HE9 HE29 Hfix.
+ runC LAWS HS HJ UOFF_X. leafC HS HJ HA HE18 HE21 HE14 HE8 HE9 HE29 Hfix.
Qed.
Lemma cbl_loop : forall (k : nat) (i bp b Lc : Z) regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0,
Z.of_nat k = lzwPos - i ->
journal ubs0_msyms MR STK sp0 FP L A mem md L A memc md ->
In (bl, Lby) (blocks L A) -> In (lz, Llz) (blocks L A) -> (bl + Lby <= lz \/ lz + Llz <= bl) ->
(forall a, bl <= a < bl + Lby -> inFP FP a) ->
cbl_regs_fix_u regs bl lz D C0 -> cbl_fix Lby Llz lzwPos D C0 ->
getr regs 8 = Z_to_bv 64 (lz + 2 * i) -> getr regs 9 = Z_to_bv 64 (lz + 2 * i) -> getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
getr regs 15 = Z_to_bv 64 bp -> getr regs 20 = Z_to_bv 64 b -> getr regs 18 = Z_to_bv 64 Lc ->
0 <= i < lzwPos -> 0 <= bp -> 8 * bp + b <= 12 * i -> 0 <= b <= 7 -> 0 <= Lc <= 12 ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 (ubs0_A_create_byte_list + UOFF_A)) memc (seg_rom ubs0segs)) md)
(fun c' => exists regs' mem' bp' b' corr,
c' = mkCfg (mkst regs' (Z_to_bv 64 (ubs0_A_create_byte_list + UOFF_X)) mem' (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR STK sp0 FP L A mem md L A mem' md /\
(forall x : word, bv_unsigned x < bl \/ bl + Lby <= bv_unsigned x -> mem' x = memc x) /\
mem_grows memc mem' /\
getr regs' 15 = Z_to_bv 64 bp' /\ getr regs' 22 = Z_to_bv 64 corr /\
(corr = 0 \/ (corr = -1 /\ 1 <= bp')) /\ 0 <= bp' /\ 0 <= b' /\ 8 * bp' + b' <= 12 * lzwPos /\
(forall r, In r KEPTU -> getr regs' r = getr regs r)).
Proof using IMG LAWS.
induction k as [|k IH]; intros i bp b Lc regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0
Hk HJ Hbl Hlz Hdisj HFP Hfix Hcf H8 H9 H29 H15 H20 H18 Hi Hbp Hinv Hb HLc; [lia|].
pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
assert (Hbp29 : bp < 2 ^ 29) by lia.
assert (HbpL : bp + 3 <= Lby) by lia.
eapply SR_bind.
{ eapply (cbl_segA regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b Lc); try eassumption; lia. }
cbv beta. intros c1 (regsA & memA & L1 & -> & HJA & HmA & HfixA & H8A & H9A & H29A & H15A & H20A & H18A & HL1 & HKA).
eapply SR_bind.
{ eapply (cbl_segB regsA memA STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b L1); try eassumption; lia. }
cbv beta. intros c2 (regsB & memB & s & corr & -> & HJB & HmB & HgB & HfixB & H8B & H9B & H29B & H15B & H18B & H21B & H22B & Hcorr & Hs & Hsb & HKB).
eapply SR_bind.
{ eapply (cbl_segC regsB memB STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i (bp + s) (b + L1) L1); try eassumption; lia. }
cbv beta. intros c3 (regsC & memC & b' & m & L2 & -> & HJC & HmC & HfixC & H8C & H9C & H29C & H15C & H22C & H20C & H18C & Htm & Hb' & HL2 & HKC).
assert (Hms : m = s) by lia.
assert (Hmem : forall x : word, bv_unsigned x < bl \/ bl + Lby <= bv_unsigned x -> memC x = memc x).
{ intros x Hx. rewrite HmC, HmB, HmA; [reflexivity|]. lia. }
assert (Hgr : mem_grows memc memC).
{ eapply mem_grows_trans; [apply (mem_grows_of_eq memc memA HmA)|].
eapply mem_grows_trans; [exact HgB | apply (mem_grows_of_eq memB memC HmC)]. }
assert (HK : forall r, In r KEPTU -> getr regsC r = getr regs r).
{ intros r Hr. rewrite HKC, HKB, HKA by exact Hr. reflexivity. }
destruct (Z.eqb_spec (i + 1) lzwPos) as [Heq | Hne].
-
apply SR_ret. exists regsC, memC, (bp + s), b', corr.
split; [reflexivity|]. split; [exact HJC|]. split; [exact Hmem|]. split; [exact Hgr|].
split; [exact H15C|]. split; [rewrite H22C; exact H22B|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exact HK.
-
eapply SR_mono.
{ eapply (IH (i + 1) (bp + s) b' L2 regsC memC STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0);
try eassumption; lia. }
cbv beta. intros c' (regs' & mem' & bp' & b'' & corr' & -> & HJ' & Hm' & Hg' & H15' & H22' & Hcorr' & Hbp' & Hb'' & Hinv' & HK').
exists regs', mem', bp', b'', corr'.
split; [reflexivity|]. split; [exact HJ'|].
split; [intros x Hx; rewrite Hm' by exact Hx; apply Hmem; exact Hx|].
split; [eapply mem_grows_trans; [exact Hgr | exact Hg']|].
split; [exact H15'|]. split; [exact H22'|].
split; [exact Hcorr'|]. split; [exact Hbp'|]. split; [exact Hb''|]. split; [exact Hinv'|].
intros r Hr. rewrite HK' by exact Hr. apply HK. exact Hr.
Qed.
Definition ss_cbl : sstate :=
mkSS ubs0_A_create_byte_list sr_atoms
[ YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 [];
YP09.mkRegion (Some 10%nat) 0 1 0 1 [] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + CBL_STK_U) (2^63) 4); (10%nat, mkAF 4096 CEIL_MAX 4);
(11%nat, mkAF 0 (2^28) 0); (12%nat, mkAF 4096 CEIL_MAX 4); (13%nat, mkAF 0 65535 0); (14%nat, mkAF 0 12 0);
(32%nat, NOTBL) ]
[] [ (SAlu ALU_XOR (SOff 10%nat 0) (SLit (-1)), SOff 32%nat 0) ]).
Definition CBL_CLOB : list reg := [5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%bv.
Lemma cbl_clob_kept : forall r : reg, reg_in r CBL_CLOB = false -> r = 0%bv \/ In r KEPTU.
Proof using.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Theorem ubs0_cbl : forall L A regs mem md bl Lby lz Llz lzwPos D C0 rest,
fn_pre ubs0_msyms MR CBL_STK_U L A regs mem md ->
getr regs 10 = Z_to_bv 64 bl -> getr regs 11 = Z_to_bv 64 lzwPos -> getr regs 12 = Z_to_bv 64 lz ->
getr regs 13 = Z_to_bv 64 D -> getr regs 14 = Z_to_bv 64 C0 ->
0 <= lzwPos < 2 ^ 28 -> 0 <= D <= 65535 -> 0 <= C0 <= 12 ->
12 * lzwPos / 8 + 3 <= Lby -> 2 * lzwPos <= Llz -> 0 < Llz ->
Permutation (blocks L A) ((bl, Lby) :: (lz, Llz) :: rest) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_create_byte_list) mem (seg_rom ubs0segs)) md)
(fun c' => exists regs' mem' ret,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md /\
journal ubs0_msyms MR CBL_STK_U (spZ regs) [(bl, bl + Lby)] L A mem md L A mem' md /\
regs_preserved regs regs' /\
getr regs' 10 = Z_to_bv 64 ret /\ 0 <= ret /\ 8 * ret <= 12 * lzwPos).
Proof using IMG LAWS.
intros L A regs mem md bl Lby lz Llz lzwPos D C0 rest HPRE H10 H11 H12 H13 H14 HlzwPos HD HC0 HLby HLlz HLlz0 HB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : CBL_STK_U = 80) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hblin : In (bl, Lby) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hlzin : In (lz, Llz) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
pose proof (Z.div_mod (12 * lzwPos) 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (12 * lzwPos) 8 ltac:(lia)) as Hmb.
set (q8 := 12 * lzwPos / 8) in *. set (r8 := (12 * lzwPos) mod 8) in *. clearbody q8 r8.
assert (HLby' : 3 * lzwPos + 5 <= 2 * Lby) by lia. assert (HLby3 : 3 <= Lby) by lia. clear Hdm Hmb HLby q8 r8.
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md bl Lby HH Hblin ltac:(lia)) as (Bl0 & Bl1 & Bl16).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md lz Llz HH Hlzin ltac:(lia)) as (Bz0 & Bz1 & Bz16).
pose proof (heap_sep_perm ubs0_msyms MR LAWS L A mem md (bl, Lby) _ (lz, Llz) HH HB ltac:(left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep.
remember (Ereg regs [Z_to_bv 64 (2 ^ 64 - 1 - bl)]) as E0 eqn:HE0.
assert (HA0 : env_agree 32 (Ereg regs [Z_to_bv 64 (2 ^ 64 - 1 - bl)]) E0) by (rewrite HE0; apply env_agree_refl).
assert (HE2 : ew E0 2 = getr regs 2) by (subst E0; apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew E0 1 = getr regs 1) by (subst E0; apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE10 : ew E0 10 = Z_to_bv 64 bl) by (subst E0; rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity); exact H10).
assert (HE11 : ew E0 11 = Z_to_bv 64 lzwPos) by (subst E0; rewrite (ew_Ereg_nat regs _ 11 11%bv) by (vm_compute; reflexivity); exact H11).
assert (HE12 : ew E0 12 = Z_to_bv 64 lz) by (subst E0; rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity); exact H12).
assert (HE13 : ew E0 13 = Z_to_bv 64 D) by (subst E0; rewrite (ew_Ereg_nat regs _ 13 13%bv) by (vm_compute; reflexivity); exact H13).
assert (HE14 : ew E0 14 = Z_to_bv 64 C0) by (subst E0; rewrite (ew_Ereg_nat regs _ 14 14%bv) by (vm_compute; reflexivity); exact H14).
assert (HE32 : ew E0 32 = Z_to_bv 64 (2 ^ 64 - 1 - bl)) by (subst E0; rewrite (ew_Ereg_extra regs _ 0); reflexivity).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
set (ms0 := mkst regs (Z_to_bv 64 ubs0_A_create_byte_list) mem (seg_rom ubs0segs)).
assert (HS : st_ok ubs0segs E0 ss_cbl ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0.
- rewrite HE0. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite HE2. exact Hspw.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE10, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (present_writable ubs0_msyms).
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bl Lby o HH Hblin ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE10, Hspw, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok, NOTBL. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE11, HE12, HE13, HE14, HE32, Hspw, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; first [exact Hal16 | exact Bl16 | exact Bz16 | lia].
+ cbn [f_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite (U_not _ 10 bl HE10), (U_atom _ 32 _ HE32) by lia. reflexivity. }
clear Hal16 Bl16 Bz16.
pose proof (journal_init ubs0_msyms MR CBL_STK_U [(bl, bl + Lby)] L A regs mem md HPRE) as HJ.
change mem with (ms_mem ms0) in HJ.
assert (Hwr : forall E' cs1 cs2, ew E' 2 = getr regs 2 -> ew E' 10 = Z_to_bv 64 bl ->
wr_ok E' [YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 cs1; YP09.mkRegion (Some 10%nat) 0 1 0 1 cs2]
CBL_STK_U (spZ regs) [(bl, bl + Lby)] (blocks L A) (blocks L A)).
{ intros E' cs1 cs2 HE2' HE10'.
eapply wr_ok_cons_stack; [reflexivity | rewrite HE2'; exact Hspw | cbn; lia | cbn; lia |].
eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 10 bl bl Lby);
[reflexivity | rewrite HE10'; apply unsigned_lit_small; lia | exact Hblin | cbn; lia | cbn; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. exists (bl, bl + Lby). split; [left; reflexivity | cbn; lia]. }
assert (Hwr1 : forall E' cs1, ew E' 2 = getr regs 2 ->
wr_ok E' [YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 cs1] CBL_STK_U (spZ regs) [(bl, bl + Lby)] (blocks L A) (blocks L A)).
{ intros E' cs1 HE2'. eapply wr_ok_cons_stack; [reflexivity | rewrite HE2'; exact Hspw | cbn; lia | cbn; lia | apply wr_ok_nil]. }
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr; [exact HE2 | exact HE10]. }
jbranch ubs0tbl HS.
-
rewrite branch_eq_U, (U_atom _ 11 lzwPos), U_lit in Hc; [| lia0 | exact HE11 | lia].
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_norm. apply Hwr; [exact HE2 | exact HE10]. }
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA0 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. jreg HS (1%bv:reg) as Hr1.
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx), 0 end.
rewrite Hr1, HE1, Hra. split; [reflexivity|]. split; [exact HJ|]. split; [exact HPR|]. split; [exact Hr10|]. lia.
-
rewrite branch_eq_U, (U_atom _ 11 lzwPos), U_lit in Hc; [| lia0 | exact HE11 | lia].
assert (Hlp : 0 < lzwPos) by (destruct (Z.eqb_spec lzwPos 0); [discriminate | lia]).
jrun_to LAWS ubs0tbl_ok HS HJ (ubs0_A_create_byte_list + UOFF_A).
{ wr_norm. apply Hwr; [exact HE2 | exact HE10]. }
jreg HS (10%bv:reg) as Hl10. jreg HS (12%bv:reg) as Hl12. jreg HS (13%bv:reg) as Hl13. jreg HS (14%bv:reg) as Hl14.
jreg HS (16%bv:reg) as Hl16. jreg HS (5%bv:reg) as Hl5. jreg HS (17%bv:reg) as Hl17. jreg HS (6%bv:reg) as Hl6.
jreg HS (7%bv:reg) as Hl7. jreg HS (28%bv:reg) as Hl28. jreg HS (31%bv:reg) as Hl31. jreg HS (30%bv:reg) as Hl30.
jreg HS (8%bv:reg) as Hl8. jreg HS (9%bv:reg) as Hl9. jreg HS (29%bv:reg) as Hl29.
jreg HS (15%bv:reg) as Hl15. jreg HS (20%bv:reg) as Hl20. jreg HS (18%bv:reg) as Hl18.
rewrite HE10 in Hl10. rewrite HE12 in Hl12. rewrite HE13 in Hl13. rewrite HE14 in Hl14.
rewrite HE13, alu64_sll1 in Hl16 by lia. rewrite HE32 in Hl5.
rewrite HE12 in Hl8. rewrite HE12 in Hl9. rewrite HE11 in Hl29. rewrite HE14 in Hl18.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (cbl_loop (Z.to_nat lzwPos) 0 0 0 C0 _ _ CBL_STK_U (spZ regs) [(bl, bl + Lby)] L A mem md bl Lby lz Llz lzwPos D C0);
[ lia | exact HJ | exact Hblin | exact Hlzin | lia
| intros a Ha; exists (bl, bl + Lby); split; [left; reflexivity | cbn; lia]
| unfold cbl_regs_fix_u; repeat split; assumption
| unfold cbl_fix; lia
| rewrite Hl8; f_equal; lia | rewrite Hl9; f_equal; lia | rewrite Hl29; f_equal; lia
| exact Hl15 | exact Hl20 | exact Hl18 | lia | lia | lia | lia | lia ]. }
cbv beta. intros c' (regsL & memL & bp' & b' & corr & -> & HJL & HmL & HgL & H15L & H22L & Hcorr & Hbp' & Hb' & Hinv & HKL).
lazymatch type of HS with
| st_ok _ ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) [0%nat]) in
pose proof (st_ok_after_stretch ubs0segs 33 E ss ms regsL memL rs (ubs0_A_create_byte_list + UOFF_X) CBL_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs 33 CBL_CLOB (ubs0_A_create_byte_list + UOFF_X)) in
change (ss_after_stretch ss rs 33 CBL_CLOB (ubs0_A_create_byte_list + UOFF_X)) with ss2 in HS2
end.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HP : P); [| assert (HQ : Q); [| specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r Hr. destruct (cbl_clob_kept r Hr) as [-> | Hin]; [rewrite !getr_zero; reflexivity | apply HKL; exact Hin]. }
{ constructor; [|constructor].
eapply (region_kept_outside _ _ _ _ _ bl Lby HmL HgL); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE2, ?Hspw; lia. }
clear HS. rename HS2 into HS.
assert (HE43 : ew (havoc E0 33 (map (getr regsL) CBL_CLOB)) 43 = Z_to_bv 64 bp').
{ rewrite <- H15L. etransitivity; [apply (ew_havoc_new E0 33 (map (getr regsL) CBL_CLOB) 10 (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
Local Ltac cbl_tail LAWS HS HJL Hwr1 HE2 HE1 HE43 HA0 Hra ret :=
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end;
jrun LAWS ubs0tbl_ok HS HJL; [ wr_norm; apply Hwr1; ew_havoc; exact HE2 |];
let HPR := fresh "HPR" in
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS (env_agree_havoc_ge 32 33 _ _ _ ltac:(lia) HA0) ltac:(vm_compute; reflexivity)) as HPR;
let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
jreg HS (10%bv:reg) as Hr10; jreg HS (1%bv:reg) as Hr1;
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
[ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJL)))
| exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJL))))
| lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx), ret end;
rewrite Hr1, HE1, Hra; split; [reflexivity|]; split; [exact HJL|]; split; [exact HPR|];
rewrite Hr10, HE43, ?unsigned_lit_small by lia; split; [f_equal; lia | lia] ].
destruct Hcorr as [Hcz | [Hcz Hbp1]]; rewrite Hcz in H22L.
+ pose proof (st_ok_set_reg ubs0segs _ _ _ 22%bv (SLit 0) HS ltac:(intros X; discriminate X) H22L) as HS1.
pose proof (st_ok_add_fact ubs0segs _ _ _ 43 (mkAF 0 (2 ^ 29) 0) HS1) as HS2.
match type of HS2 with ?P -> _ => assert (HFa : P); [| specialize (HS2 HFa); clear HFa] end.
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE43, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
clear HS HS1. rename HS2 into HS.
cbl_tail LAWS HS HJL Hwr1 HE2 HE1 HE43 HA0 Hra bp'.
+ rewrite <- lit_m1 in H22L.
pose proof (st_ok_set_reg ubs0segs _ _ _ 22%bv (SLit 18446744073709551615) HS ltac:(intros X; discriminate X) H22L) as HS1.
pose proof (st_ok_add_fact ubs0segs _ _ _ 43 (mkAF 1 (2 ^ 29) 0) HS1) as HS2.
match type of HS2 with ?P -> _ => assert (HFa : P); [| specialize (HS2 HFa); clear HFa] end.
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE43, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
clear HS HS1. rename HS2 into HS.
cbl_tail LAWS HS HJL Hwr1 HE2 HE1 HE43 HA0 Hra (bp' - 1).
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
