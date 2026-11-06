(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YI06 YI5b YI09 YI08.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07 YI00 YI0m.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI01 YI6c YI0i YI03.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma src0_errno_low_cbl : errno_addr src0_msyms + 4 <= alloc_ceiling.
Proof.   pose proof (proj1 alloc_ceiling_val). enough (errno_addr src0_msyms + 4 <= CEIL_MIN) by lia. vm_compute. intros H'. discriminate H'. Qed.
Definition OFF_A : Z := 0x4c.
Definition OFF_B : Z := 0x6c.
Definition OFF_C : Z := 0x11c.
Definition OFF_X : Z := 0x158.
Definition ss_A : sstate := mkSS (src0_A_create_byte_list + OFF_A) sr_cbl [] None (mkFacts cbl_facts_AB [] []).
Definition ss_B : sstate := mkSS (src0_A_create_byte_list + OFF_B) sr_cbl [R12; R32] None (mkFacts cbl_facts_AB [] cbl_alias).
Definition ss_C : sstate := mkSS (src0_A_create_byte_list + OFF_C) sr_cbl [R12] None (mkFacts cbl_facts_C [] []).
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Lemma atoms_ok_core : forall regs extra L A mem md bl Lby lz Llz lzwPos D C0 i bp Lc,
heap_ok MR L A mem md -> In (bl, Lby) (blocks L A) -> In (lz, Llz) (blocks L A) ->
cbl_regs_fix regs bl lz lzwPos D C0 -> cbl_fix Lby Llz lzwPos D C0 ->
getr regs 12 = Z_to_bv 64 (lz + 2 * i) -> getr regs 15 = Z_to_bv 64 bp -> getr regs 28 = Z_to_bv 64 Lc ->
0 <= i <= lzwPos -> 0 <= bp < 2 ^ 29 -> 0 <= Lc <= 12 -> 0 < Lby ->
atoms_ok (Ereg regs extra) cbl_facts_core.
Proof.
intros regs extra L A mem md bl Lby lz Llz lzwPos D C0 i bp Lc HH Hbl Hlz
(H10 & H6 & H13 & H14 & H16 & H17 & H5 & H7) (F1 & F2 & F3 & F4 & F5) H12 H15 H28 Hi Hbp HLc HLby.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (heap_blocks_range src0_msyms MR LAWS L A mem md bl Lby HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
destruct (heap_blocks_range src0_msyms MR LAWS L A mem md lz Llz HH Hlz ltac:(lia)) as (Bz0 & Bz1 & Bz16).
cbn [atoms_ok cbl_facts_core]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 10 10%bv), (ew_Ereg_nat regs _ 12 12%bv), (ew_Ereg_nat regs _ 6 6%bv),
(ew_Ereg_nat regs _ 13 13%bv), (ew_Ereg_nat regs _ 14 14%bv), (ew_Ereg_nat regs _ 16 16%bv),
(ew_Ereg_nat regs _ 15 15%bv), (ew_Ereg_nat regs _ 28 28%bv) by (vm_compute; reflexivity).
rewrite H10, H12, H6, H13, H14, H16, H15, H28, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; first [exact Bl16 | lia].
Qed.
Lemma ew_EL : forall regs P extra j (v : word),
nth_error extra j = Some v -> ew (Ereg regs (Z_to_bv 64 P :: extra)) (33 + j) = v.
Proof.
intros regs P extra j v Hj. replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra.
cbn [nth]. exact (nth_error_nth _ _ _ Hj).
Qed.
Lemma ew_EL_P : forall regs P extra, ew (Ereg regs (Z_to_bv 64 P :: extra)) 32 = Z_to_bv 64 P.
Proof. intros. rewrite (ew_Ereg_extra regs _ 0). reflexivity. Qed.
Lemma R12_ok : forall regs L A mem md lz Llz i (w1 : word),
heap_ok MR L A mem md -> In (lz, Llz) (blocks L A) ->
getr regs 12 = Z_to_bv 64 (lz + 2 * i) -> 0 <= i -> 2 * i + 2 <= Llz ->
exists X, 0 <= X < 2 ^ 16 /\
forall extra, region_ok src0segs (Ereg regs (w1 :: Z_to_bv 64 X :: extra)) mem R12.
Proof.
intros regs L A mem md lz Llz i w1 HH Hlz H12 Hi HiL.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (heap_blocks_range src0_msyms MR LAWS L A mem md lz Llz HH Hlz ltac:(lia)) as (Bz0 & Bz1 & Bz16).
destruct (val_mem2 src0segs mem (lz + 2 * i)) as (X & HX & HV).
{ apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ lz Llz (2 * i) HH Hlz ltac:(lia))). }
{ replace (lz + 2 * i + 1) with (lz + (2 * i + 1)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ lz Llz (2 * i + 1) HH Hlz ltac:(lia))). }
exists X. split; [exact HX|]. intros extra.
unfold region_ok, R12. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity). rewrite H12, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply chunk_ok_val; [| exact HX | cbn; lia | rewrite Z.add_0_r; exact HV].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 1). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma R32_ok : forall regs L A mem md bl Lby bp w2,
heap_ok MR L A mem md -> In (bl, Lby) (blocks L A) ->
0 <= bp -> bp + 3 <= Lby ->
exists Y0 Y1 Y2, 0 <= Y0 < 256 /\ 0 <= Y1 < 256 /\ 0 <= Y2 < 256 /\
forall extra, region_ok src0segs (Ereg regs (Z_to_bv 64 (bl + bp) :: w2 :: Z_to_bv 64 Y0 :: Z_to_bv 64 Y1 :: Z_to_bv 64 Y2 :: extra)) mem R32.
Proof.
intros regs L A mem md bl Lby bp w2 HH Hbl Hbp HbpL.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (heap_blocks_range src0_msyms MR LAWS L A mem md bl Lby HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
assert (HP : forall j, 0 <= j < 3 -> present mem (bl + bp + j)).
{ intros j Hj. replace (bl + bp + j) with (bl + (bp + j)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bl Lby (bp + j) HH Hbl ltac:(lia))). }
destruct (val_mem1 src0segs mem (bl + bp)) as (Y0 & HY0 & HV0); [replace (bl + bp) with (bl + bp + 0) by lia; apply HP; lia|].
destruct (val_mem1 src0segs mem (bl + bp + 1)) as (Y1 & HY1 & HV1); [apply HP; lia|].
destruct (val_mem1 src0segs mem (bl + bp + 2)) as (Y2 & HY2 & HV2); [apply HP; lia|].
exists Y0, Y1, Y2. split; [exact HY0|]. split; [exact HY1|]. split; [exact HY2|]. intros extra.
unfold region_ok, R32. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite (ew_Ereg_extra regs _ 0). cbn [nth]. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src0_msyms). apply HP. lia. }
constructor; [|constructor; [|constructor; [|constructor]]].
- eapply chunk_ok_val; [| exact HY0 | cbn; lia | rewrite Z.add_0_r; exact HV0].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 2). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- eapply chunk_ok_val; [| exact HY1 | cbn; lia | exact HV1].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 3). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- eapply chunk_ok_val; [| exact HY2 | cbn; lia | exact HV2].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 4). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma R12_okV : forall regs L A mem md lz Llz i (w1 : word) X,
heap_ok MR L A mem md -> In (lz, Llz) (blocks L A) ->
getr regs 12 = Z_to_bv 64 (lz + 2 * i) -> 0 <= i -> 2 * i + 2 <= Llz ->
val_mem src0segs mem (lz + 2 * i) 2 X -> 0 <= X < 2 ^ 16 ->
forall extra, region_ok src0segs (Ereg regs (w1 :: Z_to_bv 64 X :: extra)) mem R12.
Proof.
intros regs L A mem md lz Llz i w1 X HH Hlz H12 Hi HiL HV HX extra.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (heap_blocks_range src0_msyms MR LAWS L A mem md lz Llz HH Hlz ltac:(lia)) as (Bz0 & Bz1 & Bz16).
unfold region_ok, R12. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity). rewrite H12, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply chunk_ok_val; [| exact HX | cbn; lia | rewrite Z.add_0_r; exact HV].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 1). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma R32_okV : forall regs L A mem md bl Lby bp w2 Y0,
heap_ok MR L A mem md -> In (bl, Lby) (blocks L A) ->
0 <= bp -> bp + 3 <= Lby -> val_mem src0segs mem (bl + bp) 1 Y0 -> 0 <= Y0 < 256 ->
exists Y1 Y2, 0 <= Y1 < 256 /\ 0 <= Y2 < 256 /\
forall extra, region_ok src0segs (Ereg regs (Z_to_bv 64 (bl + bp) :: w2 :: Z_to_bv 64 Y0 :: Z_to_bv 64 Y1 :: Z_to_bv 64 Y2 :: extra)) mem R32.
Proof.
intros regs L A mem md bl Lby bp w2 Y0 HH Hbl Hbp HbpL HV0 HY0.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (heap_blocks_range src0_msyms MR LAWS L A mem md bl Lby HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
assert (HP : forall j, 0 <= j < 3 -> present mem (bl + bp + j)).
{ intros j Hj. replace (bl + bp + j) with (bl + (bp + j)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bl Lby (bp + j) HH Hbl ltac:(lia))). }
destruct (val_mem1 src0segs mem (bl + bp + 1)) as (Y1 & HY1 & HV1); [apply HP; lia|].
destruct (val_mem1 src0segs mem (bl + bp + 2)) as (Y2 & HY2 & HV2); [apply HP; lia|].
exists Y1, Y2. split; [exact HY1|]. split; [exact HY2|]. intros extra.
unfold region_ok, R32. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite (ew_Ereg_extra regs _ 0). cbn [nth]. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src0_msyms). apply HP. lia. }
constructor; [|constructor; [|constructor; [|constructor]]].
- eapply chunk_ok_val; [| change (2 ^ 8) with 256; exact HY0 | cbn; lia | rewrite Z.add_0_r; exact HV0].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 2). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- eapply chunk_ok_val; [| exact HY1 | cbn; lia | exact HV1].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 3). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- eapply chunk_ok_val; [| exact HY2 | cbn; lia | exact HV2].
cbn [sv_denot]. rewrite (ew_Ereg_extra regs _ 4). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma cbl_segAV : forall regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b Lc nreg dict,
journal src0_msyms MR STK sp0 FP L A mem md L A memc md ->
In (bl, Lby) (blocks L A) -> In (lz, Llz) (blocks L A) ->
cbl_regs_fix regs bl lz lzwPos D C0 -> cbl_fix Lby Llz lzwPos D C0 ->
getr regs 12 = Z_to_bv 64 (lz + 2 * i) -> getr regs 15 = Z_to_bv 64 bp -> getr regs 30 = Z_to_bv 64 b ->
getr regs 28 = Z_to_bv 64 Lc ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> bp + 3 <= Lby -> 0 <= b <= 7 -> 0 <= Lc <= 12 ->
getr regs 29 = Z_to_bv 64 nreg -> getr regs 11 = Z_to_bv 64 dict -> 0 <= nreg < 2 ^ 62 -> 0 <= dict < 2 ^ 31 ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 (src0_A_create_byte_list + OFF_A)) memc (seg_rom src0segs)) md)
(fun c' => exists regs' mem' L',
c' = mkCfg (mkst regs' (Z_to_bv 64 (src0_A_create_byte_list + OFF_B)) mem' (seg_rom src0segs)) md /\
journal src0_msyms MR STK sp0 FP L A mem md L A mem' md /\
(forall x, mem' x = memc x) /\
cbl_regs_fix regs' bl lz lzwPos D C0 /\
getr regs' 12 = Z_to_bv 64 (lz + 2 * i) /\ getr regs' 15 = Z_to_bv 64 bp /\ getr regs' 30 = Z_to_bv 64 b /\
getr regs' 28 = Z_to_bv 64 L' /\ 0 <= L' <= 12 /\
(forall r, In r KEPT -> getr regs' r = getr regs r) /\
(let g := (Lc <? 12) && (nreg mod 65536 - D =? dict) in
L' = (if g then Lc + 1 else Lc) /\ getr regs' 29 = Z_to_bv 64 (if g then 2 * nreg else nreg) /\ getr regs' 11 = Z_to_bv 64 dict)).
Proof.
intros regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b Lc nreg dict
HJ Hbl Hlz Hfix Hcf H12 H15 H30 H28 Hi Hbp HbpL Hb HLc H29 H11 Hnreg Hdict.
pose proof Hfix as (H10 & H6 & H13 & H14 & H16 & H17 & H5 & H7). pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HH.
destruct (heap_blocks_range src0_msyms MR LAWS L A memc md bl Lby HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
remember (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]) as E eqn:HE.
assert (HA : env_agree 32 (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]) E)
by (rewrite HE; apply env_agree_refl).
assert (HE28 : ew E 28 = Z_to_bv 64 Lc) by (rewrite HE, (ew_Ereg_nat regs _ 28 28%bv) by (vm_compute; reflexivity); exact H28).
assert (HE30 : ew E 30 = Z_to_bv 64 b) by (rewrite HE, (ew_Ereg_nat regs _ 30 30%bv) by (vm_compute; reflexivity); exact H30).
assert (HE29 : ew E 29 = Z_to_bv 64 nreg) by (rewrite HE, (ew_Ereg_nat regs _ 29 29%bv) by (vm_compute; reflexivity); exact H29).
assert (HE11 : ew E 11 = Z_to_bv 64 dict) by (rewrite HE, (ew_Ereg_nat regs _ 11 11%bv) by (vm_compute; reflexivity); exact H11).
assert (HE13 : ew E 13 = Z_to_bv 64 D) by (rewrite HE, (ew_Ereg_nat regs _ 13 13%bv) by (vm_compute; reflexivity); exact H13).
set (ms0 := mkst regs (Z_to_bv 64 (src0_A_create_byte_list + OFF_A)) memc (seg_rom src0segs)).
assert (HS : st_ok src0segs E ss_A ms0).
{ rewrite HE. apply entry_st_ok_any.
- apply regs_ok_cbl; assumption.
- reflexivity.
- constructor.
- exact I.
- split; [|split; exact I]. unfold ss_A, cbl_facts_AB. cbn [f_atoms]. apply atoms_ok_app.
+ eapply (atoms_ok_core regs _ L A memc md bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 30 30%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_extra regs _ 0), (ew_Ereg_extra regs _ 1), (ew_Ereg_extra regs _ 2), (ew_Ereg_extra regs _ 3), (ew_Ereg_extra regs _ 4).
cbn [nth]. rewrite H30, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia. }
change memc with (ms_mem ms0) in HJ.
clear Bl16.
Local Ltac leafA HS HJ HA HE HE28 HE30 Hfix HE29 Hg kept29 :=
lazymatch type of HE28 with ew ?E 28 = Z_to_bv 64 ?Lc =>
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok _ _ _ _ _ _ (KEPT ++ [10; 6; 13; 14; 16; 12; 15; 30; 11]%bv ++ kept29) HS HA ltac:(vm_compute; reflexivity)) as HK;
let H17 := fresh "Hq17" in let H5 := fresh "Hq5" in let H7 := fresh "Hq7" in let H28' := fresh "Hq28" in let H29' := fresh "Hq29" in
jreg HS (17%bv:reg) as H17; jreg HS (5%bv:reg) as H5; jreg HS (7%bv:reg) as H7; jreg HS (28%bv:reg) as H28'; jreg HS (29%bv:reg) as H29';
rewrite HE28 in H28'; rewrite ?unsigned_lit_small in H28' by lia;
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch type of H28' with getr _ _ = Z_to_bv 64 ?L' =>
lazymatch type of HS with st_ok _ _ _ ?msx =>
exists (ms_regs msx), (ms_mem msx), L' end end;
split; [reflexivity|]; split; [exact HJ|];
split; [ intros x;
repeat lazymatch goal with HF : frame_of _ [] _ _ |- _ => rewrite (frame_of_nil _ _ _ x HF); clear HF end;
reflexivity |];
destruct Hfix as (?H10 & ?H6 & ?H13 & ?H14 & ?H16 & _ & _ & _);
split; [ unfold cbl_regs_fix; repeat split; first [kreg HK | exact H17 | exact H5 | exact H7] |];
split; [kreg HK|]; split; [kreg HK|]; split; [kreg HK|];
split; [exact H28'|]; split; [lia|];
split; [intros r Hr; apply HK; apply in_app_iff; left; exact Hr|];
cbv zeta; rewrite Hg; split; [lia|]; split; [rewrite H29', HE29; first [reflexivity | apply alu64_sll1; lia] | kreg HK]
end.
jrun_to LAWS src0tbl_ok HS HJ (src0_A_create_byte_list + OFF_B). { apply wr_ok_nil. }
jbranch src0tbl HS.
-
jrun_to LAWS src0tbl_ok HS HJ (src0_A_create_byte_list + OFF_B). { apply wr_ok_nil. }
cnorm Hc HE28 HE30.
assert (Hg : ((Lc <? 12) && (nreg mod 65536 - D =? dict)) = false) by (destruct (Z.ltb_spec Lc 12); [lia | reflexivity]).
leafA HS HJ HA HE HE28 HE30 Hfix HE29 Hg [29%bv:reg].
- cnorm Hc HE28 HE30.
jrun_to LAWS src0tbl_ok HS HJ (src0_A_create_byte_list + OFF_B). { apply wr_ok_nil. }
jbranch src0tbl HS.
+ jrun_to LAWS src0tbl_ok HS HJ (src0_A_create_byte_list + OFF_B). { apply wr_ok_nil. }
rewrite branch_ne_U, (U_growcmp E 29 13 11 nreg D dict HE29 HE13 HE11) in Hc0 by lia. apply (proj1 (Bool.negb_true_iff _)) in Hc0.
assert (Hg : ((Lc <? 12) && (nreg mod 65536 - D =? dict)) = false) by (rewrite Hc0; apply Bool.andb_false_r).
leafA HS HJ HA HE HE28 HE30 Hfix HE29 Hg [29%bv:reg].
+ jrun_to LAWS src0tbl_ok HS HJ (src0_A_create_byte_list + OFF_B). { apply wr_ok_nil. }
rewrite branch_ne_U, (U_growcmp E 29 13 11 nreg D dict HE29 HE13 HE11) in Hc0 by lia. apply (proj1 (Bool.negb_false_iff _)) in Hc0.
assert (Hg : ((Lc <? 12) && (nreg mod 65536 - D =? dict)) = true) by (rewrite Hc0; destruct (Z.ltb_spec Lc 12); [reflexivity | lia]).
leafA HS HJ HA HE HE28 HE30 Hfix HE29 Hg (@nil reg).
Qed.
Lemma cbl_segBV : forall regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b Lc P Y0 X,
journal src0_msyms MR STK sp0 FP L A mem md L A memc md ->
In (bl, Lby) (blocks L A) -> In (lz, Llz) (blocks L A) -> (bl + Lby <= lz \/ lz + Llz <= bl) ->
(forall a, bl <= a < bl + Lby -> inFP FP a) ->
cbl_regs_fix regs bl lz lzwPos D C0 -> cbl_fix Lby Llz lzwPos D C0 ->
getr regs 12 = Z_to_bv 64 (lz + 2 * i) -> getr regs 15 = Z_to_bv 64 bp -> getr regs 30 = Z_to_bv 64 b ->
getr regs 28 = Z_to_bv 64 Lc ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> bp + 3 <= Lby -> 0 <= b <= 7 -> 0 <= Lc <= 12 ->
garr8 src0segs memc bl (P ++ [Y0]) -> Z.of_nat (length P) = bp -> val_mem src0segs memc (lz + 2 * i) 2 X -> 0 <= X < 65536 ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 (src0_A_create_byte_list + OFF_B)) memc (seg_rom src0segs)) md)
(fun c' => exists regs' mem' s corr,
c' = mkCfg (mkst regs' (Z_to_bv 64 (src0_A_create_byte_list + OFF_C)) mem' (seg_rom src0segs)) md /\
journal src0_msyms MR STK sp0 FP L A mem md L A mem' md /\
(forall x : word, bv_unsigned x < bl + bp \/ bl + bp + 3 <= bv_unsigned x -> mem' x = memc x) /\
mem_grows memc mem' /\
cbl_regs_fix regs' bl lz lzwPos D C0 /\
getr regs' 12 = Z_to_bv 64 (lz + 2 * i) /\ getr regs' 15 = Z_to_bv 64 (bp + s) /\ getr regs' 28 = Z_to_bv 64 Lc /\
getr regs' 31 = Z_to_bv 64 (b + Lc) /\ getr regs' 8 = Z_to_bv 64 corr /\
(corr = 0 \/ (corr = -1 /\ 1 <= s)) /\ 0 <= s <= 2 /\ 8 * s <= b + Lc < 8 * s + 8 /\
(forall r, In r KEPT -> getr regs' r = getr regs r) /\
garr8 src0segs mem' bl (rev (fst (pk_pack (Y0 :: rev P) b Lc X))) /\
Z.of_nat (length (fst (pk_pack (Y0 :: rev P) b Lc X))) = bp + s + 1 /\
corr = (if snd (pk_pack (Y0 :: rev P) b Lc X) then -1 else 0) /\
getr regs' 29 = getr regs 29 /\ getr regs' 11 = getr regs 11).
Proof.
intros regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b Lc P Y0 X
HJ Hbl Hlz Hdisj HFP Hfix Hcf H12 H15 H30 H28 Hi Hbp HbpL Hb HLc GB LenP HVX HX65.
pose proof Hfix as (H10 & H6 & H13 & H14 & H16 & H17 & H5 & H7). pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HH.
destruct (heap_blocks_range src0_msyms MR LAWS L A memc md bl Lby HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
destruct (heap_blocks_range src0_msyms MR LAWS L A memc md lz Llz HH Hlz ltac:(lia)) as (Bz0 & Bz1 & Bz16).
assert (HGY : val_mem src0segs memc (bl + bp) 1 Y0 /\ 0 <= Y0 < 256).
{ pose proof (GB (length P) ltac:(rewrite length_app; cbn [length]; lia)) as Q. rewrite app_nth2, Nat.sub_diag in Q by lia. cbn [nth] in Q. rewrite LenP in Q. exact Q. }
destruct HGY as [HVY0 HY0].
assert (HX : 0 <= X < 2 ^ 16) by (change (2 ^ 16) with 65536; lia).
pose proof (R12_okV regs L A memc md lz Llz i (Z_to_bv 64 (bl + bp)) X HH Hlz H12 ltac:(lia) ltac:(lia) HVX HX) as HR12.
destruct (R32_okV regs L A memc md bl Lby bp (Z_to_bv 64 X) Y0 HH Hbl ltac:(lia) HbpL HVY0 HY0) as (Y1 & Y2 & HY1 & HY2 & HR32).
specialize (HR12 [Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2]). specialize (HR32 (@nil word)).
remember (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 X; Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2]) as E eqn:HE.
rename HR32 into HR32'.
assert (HA : env_agree 32 (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 X; Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2]) E)
by (rewrite HE; apply env_agree_refl).
assert (HE28 : ew E 28 = Z_to_bv 64 Lc) by (rewrite HE, (ew_Ereg_nat regs _ 28 28%bv) by (vm_compute; reflexivity); exact H28).
assert (HE30 : ew E 30 = Z_to_bv 64 b) by (rewrite HE, (ew_Ereg_nat regs _ 30 30%bv) by (vm_compute; reflexivity); exact H30).
assert (HE15 : ew E 15 = Z_to_bv 64 bp) by (rewrite HE, (ew_Ereg_nat regs _ 15 15%bv) by (vm_compute; reflexivity); exact H15).
assert (HE10 : ew E 10 = Z_to_bv 64 bl) by (rewrite HE, (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity); exact H10).
assert (HE12 : ew E 12 = Z_to_bv 64 (lz + 2 * i)) by (rewrite HE, (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity); exact H12).
assert (HE32 : ew E 32 = Z_to_bv 64 (bl + bp)) by (rewrite HE, (ew_Ereg_extra regs _ 0); reflexivity).
set (ms0 := mkst regs (Z_to_bv 64 (src0_A_create_byte_list + OFF_B)) memc (seg_rom src0segs)).
assert (HS : st_ok src0segs E ss_B ms0).
{ apply entry_st_ok_any.
- rewrite HE. apply regs_ok_cbl; assumption.
- vm_compute. reflexivity.
- constructor; [exact HR12 | constructor; [exact HR32' | constructor]].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, R12, R32. cbn [r_base r_lo r_hi base_val].
rewrite HE12, HE32, !unsigned_lit_small by lia. repeat split. lia.
- split; [|split; [exact I|]].
+ unfold ss_B, cbl_facts_AB. cbn [f_atoms]. apply atoms_ok_app.
* rewrite HE. eapply (atoms_ok_core regs _ L A memc md bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
* cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE30, HE32. rewrite HE, (ew_Ereg_extra regs _ 1), (ew_Ereg_extra regs _ 2), (ew_Ereg_extra regs _ 3), (ew_Ereg_extra regs _ 4).
cbn [nth]. rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia.
+ cbn [f_alias ss_B cbl_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 10 bl HE10), (U_atom E 15 bp HE15), (U_atom E 32 (bl + bp) HE32) by lia.
apply zcanon_id. unfold M64. lia. }
change memc with (ms_mem ms0) in HJ. change memc with (ms_mem ms0). clear Bl16 Bz16.
assert (Hwr : forall E' cs1 cs2, ew E' 32 = Z_to_bv 64 (bl + bp) ->
wr_ok E' [YP09.mkRegion (Some 12%nat) 0 2 0 0 cs1; YP09.mkRegion (Some 32%nat) 0 3 0 3 cs2]
STK sp0 FP (blocks L A) (blocks L A)).
{ intros E' cs1 cs2 HE32'. apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 32 (bl + bp) bl Lby);
[reflexivity | rewrite HE32'; apply unsigned_lit_small; lia | exact Hbl | cbn; lia | cbn; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. apply HFP. lia. }
assert (HE33 : ew E 33 = Z_to_bv 64 X) by (rewrite HE, (ew_Ereg_extra regs _ 1); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 Y0) by (rewrite HE, (ew_Ereg_extra regs _ 2); reflexivity).
Local Ltac vbyteB HS HE32 HE33 HE34 HE30 k :=
lazymatch type of HS with st_ok _ ?EF _ ?msF =>
lazymatch type of HE32 with ew _ 32 = Z_to_bv 64 ?base =>
change 1%nat with (N.to_nat 1);
eapply (vval_mem_of_chunk_mod src0segs EF _ _ 32%nat base k 1%N);
[ eapply (vst_ok_region_nth src0segs _ _ _ 1 _ HS); reflexivity | reflexivity
| cbn [r_chunks In]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity]
| rewrite HE32; apply unsigned_lit_small; lia
| first [ apply (U_byte0 EF 34 33 30 _ _ _ HE34 HE33 HE30); lia
| apply (U_spill EF 33 30 _ _ 8 HE33 HE30); [lia | lia | left; reflexivity]
| apply (U_spill EF 33 30 _ _ 16 HE33 HE30); [lia | lia | right; reflexivity]
| reflexivity ]
| cbn; lia ] end end.
Local Ltac leafB HS HJ HA HE28 HE30 HE15 HE32 Hfix GB LenP HE33 HE34 :=
lazymatch type of HE15 with ew ?E 15 = Z_to_bv 64 ?bp =>
lazymatch type of HE32 with ew _ 32 = Z_to_bv 64 (?bl + _) =>
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok _ _ _ _ _ _ (KEPT ++ [10; 6; 13; 14; 16; 12; 28; 29; 11]%bv) HS HA ltac:(vm_compute; reflexivity)) as HK;
let H17 := fresh "Hq17" in let H5 := fresh "Hq5" in let H7 := fresh "Hq7" in
let Hq15 := fresh "Hq15" in let Hq8 := fresh "Hq8" in let Hq31 := fresh "Hq31" in
jreg HS (17%bv:reg) as H17; jreg HS (5%bv:reg) as H5; jreg HS (7%bv:reg) as H7;
jreg HS (15%bv:reg) as Hq15; jreg HS (8%bv:reg) as Hq8;
rewrite HE15 in Hq15; rewrite ?unsigned_lit_small in Hq15 by lia;
lazymatch type of Hq15 with _ = Z_to_bv 64 bp => rewrite <- (Z.add_0_r bp) in Hq15 | _ => idtac end;
rewrite ?lit_m1 in Hq8;
pose proof (st_ok_reg_U _ _ _ _ 31%bv HS) as Hq31;
lazymatch type of Hq31 with _ = Z_to_bv 64 (U _ (sr_get ?sr ?r)) =>
let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e in Hq31 end;
rewrite (U_t6 _ 28 _ _ 30 _ HE28 HE30) in Hq31 by lia; rewrite ?Z.add_0_r in Hq31;
let FR := fresh "FR" in
lazymatch type of HS with st_ok _ _ _ ?msx => lazymatch type of GB with garr8 _ ?m0 _ _ =>
assert (FR : forall x : word, bv_unsigned x < bl + bp \/ bl + bp + 3 <= bv_unsigned x -> ms_mem msx x = m0 x)
by (intros x Hx;
repeat lazymatch goal with HF : frame_of _ (_ :: _) _ ?m2 |- ?m3 x = _ =>
lazymatch m3 with context [m2] =>
rewrite (frame_of_one _ _ _ _ (bl + bp) (bl + bp + 3) x (frame_of_cons_ro _ _ _ _ _ HF ltac:(cbn; lia)));
[ clear HF | cbn [r_base r_wlo r_whi base_val]; ew_havoc; rewrite HE32, unsigned_lit_small by lia; lia
| cbn [r_base r_wlo r_whi base_val]; ew_havoc; rewrite HE32, unsigned_lit_small by lia; lia | exact Hx ] end end;
reflexivity) end end;
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch type of HS with st_ok _ _ _ ?msx =>
eexists (ms_regs msx), (ms_mem msx), _, _ end;
split; [reflexivity|]; split; [exact HJ|];
split; [ exact FR |];
split; [ repeat lazymatch goal with HG : mem_grows _ ?m2 |- mem_grows _ ?m3 =>
first [ exact HG | eapply mem_grows_trans; [|exact HG]; clear HG ] end |];
destruct Hfix as (?H10 & ?H6 & ?H13 & ?H14 & ?H16 & _ & _ & _);
split; [ unfold cbl_regs_fix; repeat split; first [kreg HK | exact H17 | exact H5 | exact H7] |];
split; [kreg HK|]; split; [exact Hq15|]; split; [kreg HK|]; split; [exact Hq31|]; split; [exact Hq8|];
split; [lia|]; split; [lia|]; split; [lia|];
split; [intros r Hr; apply HK; apply in_app_iff; left; exact Hr|];
let ESH := fresh "ESH" in let ECR := fresh "ECR" in
lazymatch goal with |- garr8 _ _ _ (rev (fst (pk_pack (?Y0 :: rev ?P) ?b ?Lc ?X))) /\ _ =>
destruct (pk_pack_shape P Y0 b Lc X) as [ESH ECR]; cbv zeta in ESH, ECR;
rewrite ECR, <- (length_rev (fst (pk_pack (Y0 :: rev P) b Lc X))), ESH end;
repeat match goal with |- context [?a <? ?c] => destruct (Z.ltb_spec a c); try lia | |- context [?a =? ?c] => destruct (Z.eqb_spec a c); try lia end;
cbn [orb];
split; [ apply garr8_app; split;
[ eapply garr8_frame; [exact (proj1 (proj1 (garr8_app src0segs _ _ _ _) GB))|];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold mbyte; rewrite (FR (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia); reflexivity
| rewrite LenP;
repeat (apply garr8_cons; [ first [ replace (bl + bp) with (bl + bp + 0) at 1 by lia; vbyteB HS HE32 HE33 HE34 HE30 0
| vbyteB HS HE32 HE33 HE34 HE30 1
| replace (bl + bp + 1 + 1) with (bl + bp + 2) by lia; vbyteB HS HE32 HE33 HE34 HE30 2 ]
| first [ apply lor_byte; [lia | apply Z.mod_pos_bound; lia] | apply Z.mod_pos_bound; lia | lia ] |]);
apply garr8_nil ]
| split; [rewrite length_app; cbn [length]; lia | split; [reflexivity | split; kreg HK]] ]
end end.
Local Ltac runB LAWS HS HJ Hwr HE32 := jrun_to LAWS src0tbl_ok HS HJ (src0_A_create_byte_list + OFF_C); [wr_norm; apply Hwr; ew_havoc; exact HE32|].
runB LAWS HS HJ Hwr HE32.
jbranch src0tbl HS; cnorm Hc HE28 HE30; runB LAWS HS HJ Hwr HE32.
-   leafB HS HJ HA HE28 HE30 HE15 HE32 Hfix GB LenP HE33 HE34.
- jbranch src0tbl HS; cnorm Hc0 HE28 HE30; runB LAWS HS HJ Hwr HE32.
+   jbranch src0tbl HS; cnorm Hc1 HE28 HE30; runB LAWS HS HJ Hwr HE32.
*   jbranch src0tbl HS; cnorm Hc2 HE28 HE30; runB LAWS HS HJ Hwr HE32.
--   leafB HS HJ HA HE28 HE30 HE15 HE32 Hfix GB LenP HE33 HE34.
--   leafB HS HJ HA HE28 HE30 HE15 HE32 Hfix GB LenP HE33 HE34.
*   leafB HS HJ HA HE28 HE30 HE15 HE32 Hfix GB LenP HE33 HE34.
+   leafB HS HJ HA HE28 HE30 HE15 HE32 Hfix GB LenP HE33 HE34.
Qed.
Lemma cbl_segCV : forall regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp t Lc X nreg dict,
journal src0_msyms MR STK sp0 FP L A mem md L A memc md ->
In (bl, Lby) (blocks L A) -> In (lz, Llz) (blocks L A) ->
cbl_regs_fix regs bl lz lzwPos D C0 -> cbl_fix Lby Llz lzwPos D C0 ->
getr regs 12 = Z_to_bv 64 (lz + 2 * i) -> getr regs 15 = Z_to_bv 64 bp -> getr regs 28 = Z_to_bv 64 Lc ->
getr regs 31 = Z_to_bv 64 t ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> 0 <= t <= 19 -> 0 <= Lc <= 12 ->
val_mem src0segs memc (lz + 2 * i) 2 X -> 0 <= X < 65536 ->
getr regs 29 = Z_to_bv 64 nreg -> getr regs 11 = Z_to_bv 64 dict -> 0 <= nreg < 2 ^ 62 -> 0 <= dict < 2 ^ 31 - 1 ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 (src0_A_create_byte_list + OFF_C)) memc (seg_rom src0segs)) md)
(fun c' => exists regs' mem' b' m L',
c' = mkCfg (mkst regs' (Z_to_bv 64 (src0_A_create_byte_list + (if i + 1 =? lzwPos then OFF_X else OFF_A))) mem' (seg_rom src0segs)) md /\
journal src0_msyms MR STK sp0 FP L A mem md L A mem' md /\
(forall x, mem' x = memc x) /\
cbl_regs_fix regs' bl lz lzwPos D C0 /\
getr regs' 12 = Z_to_bv 64 (lz + 2 * (i + 1)) /\ getr regs' 15 = Z_to_bv 64 bp /\ getr regs' 8 = getr regs 8 /\
getr regs' 30 = Z_to_bv 64 b' /\ getr regs' 28 = Z_to_bv 64 L' /\
t = 8 * m + b' /\ 0 <= b' < 8 /\ 0 <= L' <= 12 /\
(forall r, In r KEPT -> getr regs' r = getr regs r) /\
L' = (if X =? D then C0 else Lc) /\ getr regs' 29 = Z_to_bv 64 (if X =? D then 2 * D else nreg) /\
getr regs' 11 = Z_to_bv 64 (if X =? D then 1 else dict + 1)).
Proof.
intros regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp t Lc X nreg dict
HJ Hbl Hlz Hfix Hcf H12 H15 H28 H31 Hi Hbp Ht HLc HVX HX65 H29 H11 Hnreg Hdict.
pose proof Hfix as (H10 & H6 & H13 & H14 & H16 & H17 & H5 & H7). pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HH.
destruct (heap_blocks_range src0_msyms MR LAWS L A memc md bl Lby HH Hbl ltac:(lia)) as (Bl0 & Bl1 & Bl16).
destruct (heap_blocks_range src0_msyms MR LAWS L A memc md lz Llz HH Hlz ltac:(lia)) as (Bz0 & Bz1 & Bz16).
assert (HX : 0 <= X < 2 ^ 16) by (change (2 ^ 16) with 65536; lia).
pose proof (R12_okV regs L A memc md lz Llz i (Z_to_bv 64 0) X HH Hlz H12 ltac:(lia) ltac:(lia) HVX HX) as HR12.
specialize (HR12 (@nil word)).
remember (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 X]) as E eqn:HE.
assert (HA : env_agree 32 (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 X]) E) by (rewrite HE; apply env_agree_refl).
assert (HE28 : ew E 28 = Z_to_bv 64 Lc) by (rewrite HE, (ew_Ereg_nat regs _ 28 28%bv) by (vm_compute; reflexivity); exact H28).
assert (HE31 : ew E 31 = Z_to_bv 64 t) by (rewrite HE, (ew_Ereg_nat regs _ 31 31%bv) by (vm_compute; reflexivity); exact H31).
assert (HE14 : ew E 14 = Z_to_bv 64 C0) by (rewrite HE, (ew_Ereg_nat regs _ 14 14%bv) by (vm_compute; reflexivity); exact H14).
assert (HE12 : ew E 12 = Z_to_bv 64 (lz + 2 * i)) by (rewrite HE, (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity); exact H12).
assert (HE6 : ew E 6 = Z_to_bv 64 (lz + 2 * lzwPos)) by (rewrite HE, (ew_Ereg_nat regs _ 6 6%bv) by (vm_compute; reflexivity); exact H6).
assert (HE33 : ew E 33 = Z_to_bv 64 X) by (rewrite HE, (ew_Ereg_extra regs _ 1); reflexivity).
assert (HE13 : ew E 13 = Z_to_bv 64 D) by (rewrite HE, (ew_Ereg_nat regs _ 13 13%bv) by (vm_compute; reflexivity); exact H13).
assert (HE16 : ew E 16 = Z_to_bv 64 (2 * D)) by (rewrite HE, (ew_Ereg_nat regs _ 16 16%bv) by (vm_compute; reflexivity); exact H16).
assert (HE29 : ew E 29 = Z_to_bv 64 nreg) by (rewrite HE, (ew_Ereg_nat regs _ 29 29%bv) by (vm_compute; reflexivity); exact H29).
assert (HE11 : ew E 11 = Z_to_bv 64 dict) by (rewrite HE, (ew_Ereg_nat regs _ 11 11%bv) by (vm_compute; reflexivity); exact H11).
set (ms0 := mkst regs (Z_to_bv 64 (src0_A_create_byte_list + OFF_C)) memc (seg_rom src0segs)).
assert (HS : st_ok src0segs E ss_C ms0).
{ apply entry_st_ok_any.
- rewrite HE. apply regs_ok_cbl; assumption.
- vm_compute. reflexivity.
- constructor; [exact HR12 | constructor].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I].
unfold ss_C, cbl_facts_C. cbn [f_atoms]. apply atoms_ok_app.
+ rewrite HE. eapply (atoms_ok_core regs _ L A memc md bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE31. rewrite HE, (ew_Ereg_extra regs _ 1). cbn [nth]. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
change memc with (ms_mem ms0) in HJ. change memc with (ms_mem ms0). clear Bl16 Bz16.
Local Ltac leafC HS HJ HA HE28 HE31 HE14 HE12 HE6 Hfix Ht HE33 HE13 HE16 HE29 HE11 :=
lazymatch type of HE31 with ew ?E 31 = Z_to_bv 64 ?t =>
lazymatch type of HE12 with ew _ 12 = Z_to_bv 64 (?lz + 2 * ?i) =>
lazymatch type of HE6 with ew _ 6 = Z_to_bv 64 (_ + 2 * ?lzwPos) =>
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok _ _ _ _ _ _ (KEPT ++ [10; 6; 13; 14; 16; 15; 8]%bv) HS HA ltac:(vm_compute; reflexivity)) as HK;
let H17 := fresh "Hq17" in let H5 := fresh "Hq5" in let H7 := fresh "Hq7" in
let Hq12 := fresh "Hq12" in let Hq28 := fresh "Hq28" in let Hq30 := fresh "Hq30" in let Hq29 := fresh "Hq29" in let Hq11 := fresh "Hq11" in
jreg HS (17%bv:reg) as H17; jreg HS (5%bv:reg) as H5; jreg HS (7%bv:reg) as H7;
jreg HS (12%bv:reg) as Hq12; jreg HS (28%bv:reg) as Hq28; jreg HS (29%bv:reg) as Hq29;
pose proof (st_ok_reg_U _ _ _ _ 11%bv HS) as Hq11;
lazymatch type of Hq11 with _ = Z_to_bv 64 (U _ (sr_get ?sr ?r)) =>
let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e in Hq11 end;
first [rewrite (U_addw1 _ 11 _ HE11) in Hq11 by lia | rewrite U_lit in Hq11 by lia];
lazymatch type of HE33 with ew _ 33 = Z_to_bv 64 ?X => lazymatch type of HE13 with ew _ 13 = Z_to_bv 64 ?D =>
repeat match goal with Hcx : branch_taken _ (sv_denot _ (SOff 33 0)) (sv_denot _ (SOff 13 0)) = _ |- _ =>
rewrite branch_ne_U, (U_atom _ 33 X HE33), (U_atom _ 13 D HE13) in Hcx by lia;
first [ apply (proj1 (Bool.negb_true_iff _)) in Hcx | apply (proj1 (Bool.negb_false_iff _)) in Hcx ] end end end;
rewrite HE12, unsigned_lit_small in Hq12 by lia;
first [rewrite HE28 in Hq28 | rewrite HE14 in Hq28];
pose proof (st_ok_reg_U _ _ _ _ 30%bv HS) as Hq30;
lazymatch type of Hq30 with _ = Z_to_bv 64 (U _ (sr_get ?sr ?r)) =>
let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e in Hq30 end;
rewrite U_and_lit in Hq30 by lia0; rewrite (U_atom _ 31 t HE31) in Hq30 by lia;
let m := fresh "m" in let Hm := fresh "Hm" in
destruct (land7_split t ltac:(lia)) as (m & Hm);
repeat match goal with Hc : branch_taken _ (sv_denot _ (SOff 12 2)) (sv_denot _ (SOff 6 0)) = _ |- _ =>
first [rewrite branch_ne_U in Hc | rewrite branch_eq_U in Hc];
rewrite (U_atom_off _ 12 (lz + 2 * i) 2 HE12), (U_atom _ 6 (lz + 2 * lzwPos) HE6) in Hc by lia;
first [ apply (proj1 (Bool.negb_true_iff _)) in Hc | apply (proj1 (Bool.negb_false_iff _)) in Hc | idtac ];
first [ apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc ] end;
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch type of Hq28 with _ = Z_to_bv 64 ?L' =>
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
destruct Hfix as (?H10 & ?H6 & ?H13 & ?H14 & ?H16 & _ & _ & _);
split; [ unfold cbl_regs_fix; repeat split; first [kreg HK | exact H17 | exact H5 | exact H7] |];
split; [rewrite Hq12; f_equal; lia|]; split; [kreg HK|]; split; [apply HK; cbv; tauto|];
split; [exact Hq30|]; split; [exact Hq28|];
split; [lia|]; split; [lia|]; split; [lia|];
split; [intros r Hr; apply HK; apply in_app_iff; left; exact Hr|];
match goal with Hcx : (?xx =? ?dd) = _ |- context [?xx =? ?dd] => rewrite Hcx end;
split; [reflexivity|]; split;
[ rewrite Hq29; first [exact HE29 | exact HE16] | exact Hq11 ]
end end end.
Local Ltac runC LAWS HS HJ tgt := jrun_to LAWS src0tbl_ok HS HJ (src0_A_create_byte_list + tgt); [wr_norm; apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil] |].
runC LAWS HS HJ OFF_A.
jbranch src0tbl HS; runC LAWS HS HJ OFF_A.
-
jbranch src0tbl HS.
+ runC LAWS HS HJ OFF_A. leafC HS HJ HA HE28 HE31 HE14 HE12 HE6 Hfix Ht HE33 HE13 HE16 HE29 HE11.
+ runC LAWS HS HJ OFF_X. leafC HS HJ HA HE28 HE31 HE14 HE12 HE6 Hfix Ht HE33 HE13 HE16 HE29 HE11.
-
jbranch src0tbl HS.
+ runC LAWS HS HJ OFF_A. leafC HS HJ HA HE28 HE31 HE14 HE12 HE6 Hfix Ht HE33 HE13 HE16 HE29 HE11.
+ runC LAWS HS HJ OFF_X. leafC HS HJ HA HE28 HE31 HE14 HE12 HE6 Hfix Ht HE33 HE13 HE16 HE29 HE11.
Qed.
Definition cbl_rel (m : word -> option byte) (bl : Z) (pk : pk_st) (bp b Lc nreg dict : Z) : Prop :=
p_len pk = Lc /\ p_off pk = b /\ p_n pk = nreg mod 65536 /\ p_dict pk = dict /\
garr8 src0segs m bl (rev (p_bl pk)) /\ Z.of_nat (length (p_bl pk)) = bp + 1 /\
0 <= nreg <= 131070 * 2 ^ Lc /\ 1 <= dict.
Lemma cbl_loopV : forall (k : nat) (i bp b Lc : Z) regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 codes pk nreg dict,
Z.of_nat k = lzwPos - i ->
journal src0_msyms MR STK sp0 FP L A mem md L A memc md ->
In (bl, Lby) (blocks L A) -> In (lz, Llz) (blocks L A) -> (bl + Lby <= lz \/ lz + Llz <= bl) ->
(forall a, bl <= a < bl + Lby -> inFP FP a) ->
cbl_regs_fix regs bl lz lzwPos D C0 -> cbl_fix Lby Llz lzwPos D C0 ->
getr regs 12 = Z_to_bv 64 (lz + 2 * i) -> getr regs 15 = Z_to_bv 64 bp -> getr regs 30 = Z_to_bv 64 b ->
getr regs 28 = Z_to_bv 64 Lc ->
0 <= i < lzwPos -> 0 <= bp -> 8 * bp + b <= 12 * i -> 0 <= b <= 7 -> 0 <= Lc <= 12 ->
arr16 src0segs memc lz codes -> Z.of_nat (length codes) = lzwPos ->
getr regs 29 = Z_to_bv 64 nreg -> getr regs 11 = Z_to_bv 64 dict -> dict <= i + 1 ->
cbl_rel memc bl pk bp b Lc nreg dict ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 (src0_A_create_byte_list + OFF_A)) memc (seg_rom src0segs)) md)
(fun c' => exists regs' mem' bp' b' corr,
c' = mkCfg (mkst regs' (Z_to_bv 64 (src0_A_create_byte_list + OFF_X)) mem' (seg_rom src0segs)) md /\
journal src0_msyms MR STK sp0 FP L A mem md L A mem' md /\
(forall x : word, bv_unsigned x < bl \/ bl + Lby <= bv_unsigned x -> mem' x = memc x) /\
mem_grows memc mem' /\
getr regs' 15 = Z_to_bv 64 bp' /\ getr regs' 8 = Z_to_bv 64 corr /\
(corr = 0 \/ (corr = -1 /\ 1 <= bp')) /\ 0 <= bp' /\ 0 <= b' /\ 8 * bp' + b' <= 12 * lzwPos /\
(forall r, In r KEPT -> getr regs' r = getr regs r) /\
garr8 src0segs mem' bl (rev (p_bl (fold_left (pk_step D C0) (skipn (Z.to_nat i) codes) pk))) /\
Z.of_nat (length (p_bl (fold_left (pk_step D C0) (skipn (Z.to_nat i) codes) pk))) = bp' + 1 /\
corr = (if p_corr (fold_left (pk_step D C0) (skipn (Z.to_nat i) codes) pk) then -1 else 0)).
Proof.
induction k as [|k IH]; intros i bp b Lc regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 codes pk nreg dict
Hk HJ Hbl Hlz Hdisj HFP Hfix Hcf H12 H15 H30 H28 Hi Hbp Hinv Hb HLc ACD LenC H29 H11 Hdi HREL; [lia|].
pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
assert (Hbp29 : bp < 2 ^ 29) by lia.
assert (HbpL : bp + 3 <= Lby) by lia.
destruct HREL as (RL & RO & RN & RD & GB & LenB & Rn & Rd).
destruct (ACD (Z.to_nat i) ltac:(lia)) as [HVX HX]. rewrite Z2Nat.id in HVX by lia.
set (X := nth (Z.to_nat i) codes 0) in *.
destruct (p_bl pk) as [|Y0 T] eqn:EBL; [cbn [length] in LenB; lia|].
cbn [rev] in GB. cbn [length] in LenB.
assert (LenP : Z.of_nat (length (rev T)) = bp) by (rewrite length_rev; lia).
assert (P2 : 1 <= 2 ^ Lc <= 4096).
{ split; [pose proof (Z.pow_pos_nonneg 2 Lc ltac:(lia) ltac:(lia)); lia|]. change 4096 with (2 ^ 12). apply Z.pow_le_mono_r; lia. }
eapply SR_bind.
{ eapply (cbl_segAV regs memc STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b Lc nreg dict); try eassumption; lia. }
cbv beta. intros c1 (regsA & memA & L1 & -> & HJA & HmA & HfixA & H12A & H15A & H30A & H28A & HL1 & HKA & EL1 & H29A & H11A).
set (nreg1 := if (Lc <? 12) && (nreg mod 65536 - D =? dict) then 2 * nreg else nreg) in *.
assert (Rn1 : 0 <= nreg1 <= 2 * nreg) by (subst nreg1; destruct ((Lc <? 12) && (nreg mod 65536 - D =? dict)); lia).
assert (EbA : forall a, mbyte src0segs memA a = mbyte src0segs memc a) by (intros a; unfold mbyte; rewrite HmA; reflexivity).
eapply SR_bind.
{ eapply (cbl_segBV regsA memA STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i bp b L1 (rev T) Y0 X); try eassumption; try lia.
- eapply garr8_frame; [exact GB|]. intros a _. apply EbA.
- intros kk Hkk. rewrite EbA. apply HVX. exact Hkk. }
cbv beta. intros c2 (regsB & memB & s & corr & -> & HJB & HmB & HgB & HfixB & H12B & H15B & H28B & H31B & H8B & Hcorr & Hs & Hsb & HKB
& GB' & LenB' & Ecorr & H29B & H11B).
rewrite rev_involutive in GB', LenB', Ecorr.
pose proof (heap_blocks_range src0_msyms MR LAWS L A memc md bl Lby (proj1 HJ) Hbl ltac:(lia)) as (Bl0 & Bl1 & _).
pose proof (heap_blocks_range src0_msyms MR LAWS L A memc md lz Llz (proj1 HJ) Hlz ltac:(lia)) as (Bz0 & Bz1 & _).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (EbB : forall a, lz <= a < lz + Llz -> mbyte src0segs memB a = mbyte src0segs memc a).
{ intros a Ha. rewrite <- EbA. unfold mbyte. rewrite HmB by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
eapply SR_bind.
{ eapply (cbl_segCV regsB memB STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 i (bp + s) (b + L1) L1 X nreg1 dict); try eassumption; try lia.
- intros kk Hkk. rewrite EbB by (cbn in Hkk; lia). apply HVX. exact Hkk.
- rewrite H29B. exact H29A.
- rewrite H11B. exact H11A. }
cbv beta. intros c3 (regsC & memC & b' & m & L2 & -> & HJC & HmC & HfixC & H12C & H15C & H8C & H30C & H28C & Htm & Hb' & HL2 & HKC & EL2 & H29C & H11C).
assert (Hms : m = s) by lia.
assert (Hmem : forall x : word, bv_unsigned x < bl \/ bl + Lby <= bv_unsigned x -> memC x = memc x).
{ intros x Hx. rewrite HmC, HmB, HmA; [reflexivity|]. lia. }
assert (Hgr : mem_grows memc memC).
{ eapply mem_grows_trans; [apply (mem_grows_of_eq memc memA HmA)|].
eapply mem_grows_trans; [exact HgB | apply (mem_grows_of_eq memB memC HmC)]. }
assert (HK : forall r, In r KEPT -> getr regsC r = getr regs r).
{ intros r Hr. rewrite HKC, HKB, HKA by exact Hr. reflexivity. }
destruct (pk_step_machine D C0 pk X Lc b nreg dict L1 nreg1 L2 _ _ b' m RL RO RN RD ltac:(lia) ltac:(lia) HLc ltac:(lia) Rn EL1 eq_refl EL2 eq_refl eq_refl Htm Hb')
as (SL & SO & SN & SD & SBL & SCR & RL2 & Rn2 & Rd2).
rewrite EBL in SBL, SCR.
assert (EbC : forall a, mbyte src0segs memC a = mbyte src0segs memB a) by (intros a; unfold mbyte; rewrite HmC; reflexivity).
assert (Eskip : skipn (Z.to_nat i) codes = X :: skipn (Z.to_nat (i + 1)) codes).
{ subst X. rewrite (skipn_nth_consZ codes (Z.to_nat i)) by lia. do 2 f_equal. lia. }
rewrite Eskip. cbn [fold_left].
destruct (Z.eqb_spec (i + 1) lzwPos) as [Heq | Hne].
-
rewrite (skipn_all2 codes) by lia. cbn [fold_left].
apply SR_ret. exists regsC, memC, (bp + s), b', corr.
split; [reflexivity|]. split; [exact HJC|]. split; [exact Hmem|]. split; [exact Hgr|].
split; [exact H15C|]. split; [rewrite H8C; exact H8B|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HK|].
rewrite SBL, SCR. split; [eapply garr8_frame; [exact GB'|]; intros a _; apply EbC|]. split; [exact LenB' | exact Ecorr].
-
eapply SR_mono.
{ eapply (IH (i + 1) (bp + s) b' L2 regsC memC STK sp0 FP L A mem md bl Lby lz Llz lzwPos D C0 codes (pk_step D C0 pk X) _ _);
try eassumption; try lia.
- eapply arr16_frame; [exact ACD|]. intros a Ha. rewrite EbC. apply EbB. lia.
- unfold cbl_rel. rewrite SBL. split; [exact SL|]. split; [exact SO|]. split; [exact SN|]. split; [exact SD|].
split; [eapply garr8_frame; [exact GB'|]; intros a _; apply EbC|]. split; [exact LenB'|]. split; [exact Rn2 | lia]. }
cbv beta. intros c' (regs' & mem' & bp' & b'' & corr' & -> & HJ' & Hm' & Hg' & H15' & H8' & Hcorr' & Hbp' & Hb'' & Hinv' & HK' & GF & LenF & EcF).
exists regs', mem', bp', b'', corr'.
split; [reflexivity|]. split; [exact HJ'|].
split; [intros x Hx; rewrite Hm' by exact Hx; apply Hmem; exact Hx|].
split; [eapply mem_grows_trans; [exact Hgr | exact Hg']|].
split; [exact H15'|]. split; [exact H8'|].
split; [exact Hcorr'|]. split; [exact Hbp'|]. split; [exact Hb''|]. split; [exact Hinv'|].
split; [intros r Hr; rewrite HK' by exact Hr; apply HK; exact Hr|].
split; [exact GF|]. split; [exact LenF | exact EcF].
Qed.
Definition ss_cbl : sstate :=
mkSS src0_A_create_byte_list sr_atoms
[ YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [];
YP09.mkRegion (Some 10%nat) 0 1 0 1 [] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + CBL_STK) (2^63) 4); (10%nat, mkAF 4096 CEIL_MAX 4);
(11%nat, mkAF 0 (2^28) 0); (13%nat, mkAF 0 65535 0); (14%nat, mkAF 0 12 0) ]
[] [ (SAlu ALU_ADD (SOff 12%nat 0) (SMd M_MUL (SOff 11%nat 0) (SLit 2)), SOff 32%nat 0) ]).
Definition CBL_CLOB : list reg := [5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 28; 29; 30; 31]%bv.
Lemma cbl_clob_kept : forall r : reg, reg_in r CBL_CLOB = false -> r = 0%bv \/ In r KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Theorem src0_cblV : forall L A regs mem md bl Lby lz Llz lzwPos D C0 rest codes,
fn_pre src0_msyms MR CBL_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 bl -> getr regs 11 = Z_to_bv 64 lzwPos -> getr regs 12 = Z_to_bv 64 lz ->
getr regs 13 = Z_to_bv 64 D -> getr regs 14 = Z_to_bv 64 C0 ->
0 <= lzwPos < 2 ^ 28 -> 0 <= D <= 65535 -> 0 <= C0 <= 12 ->
12 * lzwPos / 8 + 3 <= Lby -> 2 * lzwPos <= Llz -> 0 < Llz ->
Permutation (blocks L A) ((bl, Lby) :: (lz, Llz) :: rest) ->
arr16 src0segs mem lz codes -> Z.of_nat (length codes) = lzwPos ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_create_byte_list) mem (seg_rom src0segs)) md)
(fun c' => exists regs' mem' ret,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom src0segs)) md /\
journal src0_msyms MR CBL_STK (spZ regs) [(bl, bl + Lby)] L A mem md L A mem' md /\
regs_preserved regs regs' /\
getr regs' 10 = Z_to_bv 64 ret /\ 0 <= ret /\ 8 * ret <= 12 * lzwPos /\
garr8 src0segs mem' bl (create_byte_list D C0 codes) /\ Z.of_nat (length (create_byte_list D C0 codes)) = ret + 1).
Proof.
intros L A regs mem md bl Lby lz Llz lzwPos D C0 rest codes HPRE H10 H11 H12 H13 H14 HlzwPos HD HC0 HLby HLlz HLlz0 HB ACD LenC.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : CBL_STK = 32) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
assert (Hblin : In (bl, Lby) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hlzin : In (lz, Llz) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
pose proof (Z.div_mod (12 * lzwPos) 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (12 * lzwPos) 8 ltac:(lia)) as Hmb.
set (q8 := 12 * lzwPos / 8) in *. set (r8 := (12 * lzwPos) mod 8) in *. clearbody q8 r8.
assert (HLby' : 3 * lzwPos + 5 <= 2 * Lby) by lia. assert (HLby3 : 3 <= Lby) by lia. clear Hdm Hmb HLby q8 r8.
destruct (heap_blocks_range src0_msyms MR LAWS L A mem md bl Lby HH Hblin ltac:(lia)) as (Bl0 & Bl1 & Bl16).
destruct (heap_blocks_range src0_msyms MR LAWS L A mem md lz Llz HH Hlzin ltac:(lia)) as (Bz0 & Bz1 & Bz16).
pose proof (heap_sep_perm src0_msyms MR LAWS L A mem md (bl, Lby) _ (lz, Llz) HH HB ltac:(left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep.
remember (Ereg regs [Z_to_bv 64 (lz + 2 * lzwPos)]) as E0 eqn:HE0.
assert (HA0 : env_agree 32 (Ereg regs [Z_to_bv 64 (lz + 2 * lzwPos)]) E0) by (rewrite HE0; apply env_agree_refl).
assert (HE2 : ew E0 2 = getr regs 2) by (subst E0; apply (ew_Ereg_nat regs _ 2 2%bv); vm_compute; reflexivity).
assert (HE1 : ew E0 1 = getr regs 1) by (subst E0; apply (ew_Ereg_nat regs _ 1 1%bv); vm_compute; reflexivity).
assert (HE10 : ew E0 10 = Z_to_bv 64 bl) by (subst E0; rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity); exact H10).
assert (HE11 : ew E0 11 = Z_to_bv 64 lzwPos) by (subst E0; rewrite (ew_Ereg_nat regs _ 11 11%bv) by (vm_compute; reflexivity); exact H11).
assert (HE12 : ew E0 12 = Z_to_bv 64 lz) by (subst E0; rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity); exact H12).
assert (HE13 : ew E0 13 = Z_to_bv 64 D) by (subst E0; rewrite (ew_Ereg_nat regs _ 13 13%bv) by (vm_compute; reflexivity); exact H13).
assert (HE14 : ew E0 14 = Z_to_bv 64 C0) by (subst E0; rewrite (ew_Ereg_nat regs _ 14 14%bv) by (vm_compute; reflexivity); exact H14).
assert (HE32 : ew E0 32 = Z_to_bv 64 (lz + 2 * lzwPos)) by (subst E0; rewrite (ew_Ereg_extra regs _ 0); reflexivity).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
set (ms0 := mkst regs (Z_to_bv 64 src0_A_create_byte_list) mem (seg_rom src0segs)).
assert (HS : st_ok src0segs E0 ss_cbl ms0).
{ rewrite HE0. apply entry_st_ok_full; rewrite <- ?HE0.
- rewrite HE0. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack src0segs _ mem 2 (spZ regs)); [| lia | lia | intros a Ha; apply Hstw; lia].
rewrite HE2. exact Hspw.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE10, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (present_writable src0_msyms).
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ bl Lby o HH Hblin ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE10, Hspw, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE11, HE13, HE14, Hspw, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; first [exact Hal16 | exact Bl16 | lia].
+ cbn [f_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom _ 12 lz HE12), (U_atom _ 11 lzwPos HE11), (U_atom _ 32 (lz + 2 * lzwPos) HE32), U_SLit by lia.
change (zcanon 2) with 2. rewrite (zcanon_id (lzwPos * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
clear Hal16 Bl16 Bz16.
pose proof (journal_init src0_msyms MR CBL_STK [(bl, bl + Lby)] L A regs mem md HPRE) as HJ.
change mem with (ms_mem ms0) in HJ.
assert (Hwr : forall E' cs1 cs2, ew E' 2 = getr regs 2 -> ew E' 10 = Z_to_bv 64 bl ->
wr_ok E' [YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 cs1; YP09.mkRegion (Some 10%nat) 0 1 0 1 cs2]
CBL_STK (spZ regs) [(bl, bl + Lby)] (blocks L A) (blocks L A)).
{ intros E' cs1 cs2 HE2' HE10'.
eapply wr_ok_cons_stack; [reflexivity | rewrite HE2'; exact Hspw | cbn; lia | cbn; lia |].
eapply (wr_ok_cons_inblock _ _ _ _ _ _ _ _ 10 bl bl Lby);
[reflexivity | rewrite HE10'; apply unsigned_lit_small; lia | exact Hblin | cbn; lia | cbn; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. exists (bl, bl + Lby). split; [left; reflexivity | cbn; lia]. }
assert (Hwr1 : forall E' cs1, ew E' 2 = getr regs 2 ->
wr_ok E' [YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 cs1] CBL_STK (spZ regs) [(bl, bl + Lby)] (blocks L A) (blocks L A)).
{ intros E' cs1 HE2'. eapply wr_ok_cons_stack; [reflexivity | rewrite HE2'; exact Hspw | cbn; lia | cbn; lia | apply wr_ok_nil]. }
Local Ltac vback HE2 Hspw HE34 HE36 :=
repeat first
[ reflexivity
| progress cbn [ms_mem mkst]
| lazymatch goal with |- mbyte _ ?mF ?a = mbyte _ _ _ =>
match goal with
| HFx : frame_of _ _ ?m mF |- _ =>
transitivity (mbyte src0segs m a);
[ unfold mbyte; rewrite (HFx (Z_to_bv 64 a)); [reflexivity|];
rewrite unsigned_lit_small by lia;
let r0 := fresh "r0" in let Hr0' := fresh "Hr0'" in let Hin0 := fresh "Hin0" in
intros (r0 & Hr0' & Hin0); cbv [In] in Hr0';
repeat (destruct Hr0' as [<- | Hr0']; [cbn [r_base r_wlo r_whi base_val] in Hin0; repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]); rewrite ?HE2, ?Hspw, ?HE34, ?HE36, ?unsigned_lit_small in Hin0 by lia; lia |]);
destruct Hr0'
| clear HFx ]
| Houtx : forall x : word, _ -> mF x = ?m x |- _ =>
transitivity (mbyte src0segs m a);
[ unfold mbyte; rewrite (Houtx (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia); reflexivity | clear Houtx ]
end end ].
Local Ltac cbl_b0 HS HE10 :=
lazymatch type of HS with st_ok _ ?EF _ ?msF => lazymatch type of HE10 with ew _ 10 = Z_to_bv 64 ?bl =>
apply garr8_one; [|lia]; replace bl with (bl + 0) at 1 by lia; change 1%nat with (N.to_nat 1);
eapply (vval_mem_of_chunk src0segs EF _ _ 10%nat bl 0 1%N);
[ eapply (vst_ok_region_nth src0segs _ _ _ 1 _ HS); reflexivity | reflexivity | cbn [r_chunks In]; left; reflexivity
| ew_havoc; rewrite HE10; apply unsigned_lit_small; lia | cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia ] end end.
jrun LAWS src0tbl_ok HS HJ.
{ wr_norm. apply Hwr; [exact HE2 | exact HE10]. }
jbranch src0tbl HS.
-
rewrite branch_eq_U, (U_atom _ 11 lzwPos), U_lit in Hc; [| lia0 | exact HE11 | lia].
jrun LAWS src0tbl_ok HS HJ.
{ wr_norm. apply Hwr; [exact HE2 | exact HE10]. }
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS HA0 ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. jreg HS (1%bv:reg) as Hr1.
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx), 0 end.
rewrite Hr1, HE1, Hra. split; [reflexivity|]. split; [exact HJ|]. split; [exact HPR|]. split; [exact Hr10|]. split; [lia|]. split; [lia|].
assert (lzwPos = 0) by (destruct (Z.eqb_spec lzwPos 0); [assumption | discriminate]).
destruct codes as [|c0 cr]; [|cbn [length] in LenC; lia]. change (create_byte_list D C0 []) with [0]. split; [|reflexivity].
cbl_b0 HS HE10.
-
rewrite branch_eq_U, (U_atom _ 11 lzwPos), U_lit in Hc; [| lia0 | exact HE11 | lia].
assert (Hlp : 0 < lzwPos) by (destruct (Z.eqb_spec lzwPos 0); [discriminate | lia]).
jrun_to LAWS src0tbl_ok HS HJ (src0_A_create_byte_list + OFF_A).
{ wr_norm. apply Hwr; [exact HE2 | exact HE10]. }
jreg HS (10%bv:reg) as Hl10. jreg HS (6%bv:reg) as Hl6. jreg HS (13%bv:reg) as Hl13. jreg HS (14%bv:reg) as Hl14.
jreg HS (16%bv:reg) as Hl16. jreg HS (17%bv:reg) as Hl17. jreg HS (5%bv:reg) as Hl5. jreg HS (7%bv:reg) as Hl7.
jreg HS (12%bv:reg) as Hl12. jreg HS (15%bv:reg) as Hl15. jreg HS (30%bv:reg) as Hl30. jreg HS (28%bv:reg) as Hl28.
rewrite HE10 in Hl10. rewrite HE32 in Hl6. rewrite HE13 in Hl13. rewrite HE14 in Hl14.
rewrite HE13, alu64_sll1 in Hl16 by lia. rewrite HE12 in Hl12. rewrite HE14 in Hl28.
jreg HS (29%bv:reg) as Hl29. jreg HS (11%bv:reg) as Hl11. rewrite HE13, alu64_sll1 in Hl29 by lia.
set (pk0 := mkPk [0] 0 C0 ((2 * D) mod 65536) 1 false).
lazymatch type of HS with st_ok _ _ _ ?msx => assert (HREL0 : cbl_rel (ms_mem msx) bl pk0 0 0 C0 (2 * D) 1) end.
{ unfold cbl_rel. subst pk0. cbn [p_len p_off p_n p_dict p_bl rev app length].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [cbl_b0 HS HE10|]. split; [reflexivity|].
assert (1 <= 2 ^ C0) by (pose proof (Z.pow_pos_nonneg 2 C0 ltac:(lia) ltac:(lia)); lia). nia. }
lazymatch type of HS with st_ok _ _ _ ?msx => assert (ACD0 : arr16 src0segs (ms_mem msx) lz codes) end.
{ eapply arr16_frame; [exact ACD|]. intros a Ha. vback HE2 Hspw HE10 HE10. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (cbl_loopV (Z.to_nat lzwPos) 0 0 0 C0 _ _ CBL_STK (spZ regs) [(bl, bl + Lby)] L A mem md bl Lby lz Llz lzwPos D C0 codes pk0 (2 * D) 1);
[ lia | exact HJ | exact Hblin | exact Hlzin | lia
| intros a Ha; exists (bl, bl + Lby); split; [left; reflexivity | cbn; lia]
| unfold cbl_regs_fix; repeat split; assumption
| unfold cbl_fix; lia
| rewrite Hl12; f_equal; lia | exact Hl15 | exact Hl30 | exact Hl28 | lia | lia | lia | lia | lia
| exact ACD0 | exact LenC | exact Hl29 | exact Hl11 | lia | exact HREL0 ]. }
cbv beta. intros c' (regsL & memL & bp' & b' & corr & -> & HJL & HmL & HgL & H15L & H8L & Hcorr & Hbp' & Hb' & Hinv & HKL & GF & LenF & EcF).
change (skipn (Z.to_nat 0) codes) with codes in GF, LenF, EcF.
lazymatch type of HS with
| st_ok _ ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) [0%nat]) in
pose proof (st_ok_after_stretch src0segs 33 E ss ms regsL memL rs (src0_A_create_byte_list + OFF_X) CBL_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs 33 CBL_CLOB (src0_A_create_byte_list + OFF_X)) in
change (ss_after_stretch ss rs 33 CBL_CLOB (src0_A_create_byte_list + OFF_X)) with ss2 in HS2
end.
match type of HS2 with ?P -> ?Q -> _ =>
assert (HP : P); [| assert (HQ : Q); [| specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r Hr. destruct (cbl_clob_kept r Hr) as [-> | Hin]; [rewrite !getr_zero; reflexivity | apply HKL; exact Hin]. }
{ constructor; [|constructor].
eapply (region_kept_outside _ _ _ _ _ bl Lby HmL HgL); cbn [r_base r_lo r_hi r_wlo r_whi base_val];
rewrite ?HE2, ?Hspw; lia. }
clear HS. rename HS2 into HS.
assert (HE36 : ew (havoc E0 33 (map (getr regsL) CBL_CLOB)) 43 = Z_to_bv 64 bp').
{ rewrite <- H15L. etransitivity; [apply (ew_havoc_new E0 33 (map (getr regsL) CBL_CLOB) 10 (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
Local Ltac cbl_tail LAWS HS HJL Hwr1 HE2 HE1 HE36 HA0 Hra ret vfin :=
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end;
jrun LAWS src0tbl_ok HS HJL; [ wr_norm; apply Hwr1; ew_havoc; exact HE2 |];
let HPR := fresh "HPR" in
pose proof (regs_preserved_of_st_ok _ _ _ _ _ _ HS (env_agree_havoc_ge 32 33 _ _ _ ltac:(lia) HA0) ltac:(vm_compute; reflexivity)) as HPR;
let Hr10 := fresh "Hr10" in let Hr1 := fresh "Hr1" in
jreg HS (10%bv:reg) as Hr10; jreg HS (1%bv:reg) as Hr1;
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |];
[ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJL)))
| exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJL))))
| lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx), ret end;
rewrite Hr1, HE1, Hra; split; [reflexivity|]; split; [exact HJL|]; split; [exact HPR|];
rewrite Hr10, HE36, ?unsigned_lit_small by lia; split; [f_equal; lia | split; [lia | split; [lia | vfin]]] ].
destruct Hcorr as [Hcz | [Hcz Hbp1]]; rewrite Hcz in H8L.
+ pose proof (st_ok_set_reg src0segs _ _ _ 8%bv (SLit 0) HS ltac:(intros X; discriminate X) H8L) as HS1.
pose proof (st_ok_add_fact src0segs _ _ _ 43 (mkAF 0 (2 ^ 29) 0) HS1) as HS2.
match type of HS2 with ?P -> _ => assert (HFa : P); [| specialize (HS2 HFa); clear HFa] end.
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE36, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
clear HS HS1. rename HS2 into HS.
cbl_tail LAWS HS HJL Hwr1 HE2 HE1 HE36 HA0 Hra bp'
ltac:(assert (Ep : p_corr (fold_left (pk_step D C0) codes pk0) = false) by (destruct (p_corr (fold_left (pk_step D C0) codes pk0)); [lia | reflexivity]);
unfold create_byte_list; cbv zeta; fold pk0; rewrite Ep;
split; [eapply garr8_frame; [exact GF|]; intros a Ha; rewrite length_rev, LenF in Ha; vback HE2 Hspw HE2 HE2 | rewrite length_rev; exact LenF]).
+ rewrite <- lit_m1 in H8L.
pose proof (st_ok_set_reg src0segs _ _ _ 8%bv (SLit 18446744073709551615) HS ltac:(intros X; discriminate X) H8L) as HS1.
pose proof (st_ok_add_fact src0segs _ _ _ 43 (mkAF 1 (2 ^ 29) 0) HS1) as HS2.
match type of HS2 with ?P -> _ => assert (HFa : P); [| specialize (HS2 HFa); clear HFa] end.
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE36, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
clear HS HS1. rename HS2 into HS.
cbl_tail LAWS HS HJL Hwr1 HE2 HE1 HE36 HA0 Hra (bp' - 1)
ltac:(assert (Ep : p_corr (fold_left (pk_step D C0) codes pk0) = true) by (destruct (p_corr (fold_left (pk_step D C0) codes pk0)); [reflexivity | lia]);
unfold create_byte_list; cbv zeta; fold pk0; rewrite Ep;
destruct (p_bl (fold_left (pk_step D C0) codes pk0)) as [|hb tb] eqn:EBF; [cbn [length] in LenF; lia|];
cbn [tl]; cbn [rev] in GF; cbn [length] in LenF;
split; [eapply garr8_frame; [exact (proj1 (proj1 (garr8_app src0segs _ _ _ _) GF))|]; intros a Ha; rewrite length_rev in Ha; vback HE2 Hspw HE2 HE2 | rewrite length_rev; lia]).
Qed.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
