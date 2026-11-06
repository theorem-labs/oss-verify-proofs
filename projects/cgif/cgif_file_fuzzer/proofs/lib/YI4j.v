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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3b
YI06 YI5b YI09 YI08 YI0r YI0o YI1w YI3p YI3m YI3t YI3w.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 YI5c YI2z YI0j YI0k YI6c YI01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w YI2v YI3x.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_ret : sstate :=
mkSS PC_RET sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 128 0 0 (saved_chunks_at 10 128 32) ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + 8576) (2^63 - 128) 4) ] [] []).
Definition ss_ret_c : sstate := Eval vm_compute in ss_ret.
Definition ss_st : sstate :=
mkSS PC_ST sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 128 0 0 (saved_chunks_at 10 128 32) ;
YP09.mkRegion (Some 8%nat) 0 48 40 44 [] ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + 8576) (2^63 - 128) 4); (8%nat, mkAF 4096 (CEIL_MAX - 48) 4) ] [] []).
Definition ss_st_c : sstate := Eval vm_compute in ss_st.
Lemma regs_preserved_intro_std : forall regs regs' : bvmap 5 word,
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 ->
getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
regs_preserved regs regs'.
Proof. exact regs_preserved_intro_lzw. Qed.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Lemma ra_ret_R :
forall (FP : list (Z * Z)) (Q : Z -> Z -> Prop) (RP : astate -> Prop) cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte) (cur : Z) (r : word),
rcx_pre cx -> ra_origin cx regs0 ->
journal src0_msyms MR RAWADD_STK (spZ regs0) FP L A mem md L1 A1 mem1 md1 ->
st_init_done A1 = true -> RP A1 ->
Permutation (blocks L1 A1) (blocks L A) ->
obj_at src0segs mem1 (c_raw cx) LAY_Raw (rvals' cx cur) ->
frame_savedN src0_msyms 10 regs0 mem1 (spZ regs0) ->
getr regs1 2 = Z_to_bv 64 (c_sp cx) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 25 = getr regs0 25 -> getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
getr regs1 18 = r -> Q (bv_unsigned r) cur ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_RET) mem1 (seg_rom src0segs)) md1)
(ra_postR API FP Q RP cx L A mem md regs0).
Proof.
intros FP Q RP cx L A mem md L1 A1 md1 regs0 regs1 mem1 cur r Hcx (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & _) HJ Hid HRP HB HOR HFS G2 G3 G4 G25 G26 G27 G18 HQ.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof Hcx as (Hspal & Hsplo & Hcfplo & Hcfphi & _).
set (sp := c_sp cx) in *.
set (extra := savedN_vals 10 regs0).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 extra) n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX : forall j, (j < 10)%nat -> ew (Ereg regs1 extra) (32 + j)%nat = nth j (savedN_vals 10 regs0) (Z_to_bv 64 0)).
{ intros j Hj. rewrite ew_Ereg_extra. reflexivity. }
assert (HX' : forall n j, (n = 32 + j)%nat -> (j < 10)%nat -> ew (Ereg regs1 extra) n = nth j (savedN_vals 10 regs0) (Z_to_bv 64 0)).
{ intros n j -> Hj. exact (HX j Hj). }
assert (HE2 : bv_unsigned (ew (Ereg regs1 extra) 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HS : st_ok src0segs (Ereg regs1 extra) ss_ret_c (mkst regs1 (Z_to_bv 64 PC_RET) mem1 (seg_rom src0segs))).
{ change ss_ret_c with ss_ret. unfold ss_ret. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
replace sp with (spZ regs0 - 128) by lia.
apply (saved_chunks_at_ok src0_msyms 10 _ mem1 regs0 (spZ regs0) 128 32 ltac:(lia) HX HFS).
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE2.
change (2 ^ 4) with 16. repeat split; first [lia | exact Hspal]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_RET) mem1 (seg_rom src0segs))) in HJ.
jrun LAWS src0tbl_ok HS HJ; [wr_ok_tac|].
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold ra_postR.
Ltac regq HS HX' rr j :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q := fresh "Q" in
pose proof (st_ok_reg src0segs Ef ssf msf rr HS) as Q; eval_sr_get_in Q; cbn [sv_denot] in Q;
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q;
let n := eval cbv in (32 + j)%nat in
try rewrite (HX' n j eq_refl ltac:(lia)) in Q; cbn [nth savedN_vals SAVEDN SAVED firstn map fst] in Q;
cbn [ms_regs mkst]; rewrite Q; clear Q
end.
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lf ?Af _ ?mdf =>
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
exists Lf, Af, (ms_regs msf), (ms_mem msf), mdf, (bv_unsigned r), cur end end.
split. { regq HS HX' (1%bv:reg) 0%nat. rewrite Hra0. reflexivity. }
split; [exact HJ|].
split.
{ apply regs_preserved_intro_std.
- regq HS HX' (2%bv:reg) 0%nat. rewrite HE2. rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs0 2)). f_equal.
unfold spZ in Hspe. lia.
- regq HS HX' (3%bv:reg) 0%nat. rewrite (HE 3%nat 3%bv eq_refl). exact G3.
- regq HS HX' (4%bv:reg) 0%nat. rewrite (HE 4%nat 4%bv eq_refl). exact G4.
- regq HS HX' (8%bv:reg) 1%nat. reflexivity.
- regq HS HX' (9%bv:reg) 2%nat. reflexivity.
- regq HS HX' (18%bv:reg) 3%nat. reflexivity.
- regq HS HX' (19%bv:reg) 4%nat. reflexivity.
- regq HS HX' (20%bv:reg) 5%nat. reflexivity.
- regq HS HX' (21%bv:reg) 6%nat. reflexivity.
- regq HS HX' (22%bv:reg) 7%nat. reflexivity.
- regq HS HX' (23%bv:reg) 8%nat. reflexivity.
- regq HS HX' (24%bv:reg) 9%nat. reflexivity.
- regq HS HX' (25%bv:reg) 0%nat. rewrite (HE 25%nat 25%bv eq_refl). exact G25.
- regq HS HX' (26%bv:reg) 0%nat. rewrite (HE 26%nat 26%bv eq_refl). exact G26.
- regq HS HX' (27%bv:reg) 0%nat. rewrite (HE 27%nat 27%bv eq_refl). exact G27. }
split; [exact Hid|].
split. { regq HS HX' (10%bv:reg) 0%nat. rewrite (HE 18%nat 18%bv eq_refl), G18. symmetry. apply Z_to_bv_bv_unsigned. }
split; [| split; [exact HB | split; [exact HQ | exact HRP]]].
cbn [ms_mem mkst].
eapply obj_at_transport_range; [exact HOR | exact (proj1 LAY_Raw_ok) |].
intros i Hi. apply mbyte_eq_of1'.
lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _) end.
Qed.
Lemma ra_ret4_R :
forall (FP : list (Z * Z)) (Q : Z -> Z -> (word -> option byte) -> Model -> Prop) (RP : astate -> Prop) cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte) (cur : Z) (r : word),
rcx_pre cx -> ra_origin cx regs0 ->
journal src0_msyms MR RAWADD_STK (spZ regs0) FP L A mem md L1 A1 mem1 md1 ->
st_init_done A1 = true -> RP A1 ->
Permutation (blocks L1 A1) (blocks L A) ->
obj_at src0segs mem1 (c_raw cx) LAY_Raw (rvals' cx cur) ->
frame_savedN src0_msyms 10 regs0 mem1 (spZ regs0) ->
getr regs1 2 = Z_to_bv 64 (c_sp cx) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 25 = getr regs0 25 -> getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
getr regs1 18 = r -> (forall m', (forall a, 0 <= a < 2 ^ 64 -> mbyte src0segs m' a = mbyte src0segs mem1 a) -> Q (bv_unsigned r) cur m' md1) ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_RET) mem1 (seg_rom src0segs)) md1)
(ra_post4R API FP Q RP cx L A mem md regs0).
Proof.
intros FP Q RP cx L A mem md L1 A1 md1 regs0 regs1 mem1 cur r Hcx (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & _) HJ Hid HRP HB HOR HFS G2 G3 G4 G25 G26 G27 G18 HQ.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof Hcx as (Hspal & Hsplo & Hcfplo & Hcfphi & _).
set (sp := c_sp cx) in *.
set (extra := savedN_vals 10 regs0).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 extra) n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX : forall j, (j < 10)%nat -> ew (Ereg regs1 extra) (32 + j)%nat = nth j (savedN_vals 10 regs0) (Z_to_bv 64 0)).
{ intros j Hj. rewrite ew_Ereg_extra. reflexivity. }
assert (HX' : forall n j, (n = 32 + j)%nat -> (j < 10)%nat -> ew (Ereg regs1 extra) n = nth j (savedN_vals 10 regs0) (Z_to_bv 64 0)).
{ intros n j -> Hj. exact (HX j Hj). }
assert (HE2 : bv_unsigned (ew (Ereg regs1 extra) 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HS : st_ok src0segs (Ereg regs1 extra) ss_ret_c (mkst regs1 (Z_to_bv 64 PC_RET) mem1 (seg_rom src0segs))).
{ change ss_ret_c with ss_ret. unfold ss_ret. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
replace sp with (spZ regs0 - 128) by lia.
apply (saved_chunks_at_ok src0_msyms 10 _ mem1 regs0 (spZ regs0) 128 32 ltac:(lia) HX HFS).
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE2.
change (2 ^ 4) with 16. repeat split; first [lia | exact Hspal]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_RET) mem1 (seg_rom src0segs))) in HJ.
jrun LAWS src0tbl_ok HS HJ; [wr_ok_tac|].
eapply (SR_ret_at src0segs src0tbl); [exact src0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold ra_post4R.
Ltac regq4 HS HX' rr j :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q := fresh "Q" in
pose proof (st_ok_reg src0segs Ef ssf msf rr HS) as Q; eval_sr_get_in Q; cbn [sv_denot] in Q;
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q;
let n := eval cbv in (32 + j)%nat in
try rewrite (HX' n j eq_refl ltac:(lia)) in Q; cbn [nth savedN_vals SAVEDN SAVED firstn map fst] in Q;
cbn [ms_regs mkst]; rewrite Q; clear Q
end.
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lf ?Af _ ?mdf =>
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
exists Lf, Af, (ms_regs msf), (ms_mem msf), mdf, (bv_unsigned r), cur end end.
split. { regq4 HS HX' (1%bv:reg) 0%nat. rewrite Hra0. reflexivity. }
split; [exact HJ|].
split.
{ apply regs_preserved_intro_std.
- regq4 HS HX' (2%bv:reg) 0%nat. rewrite HE2. rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs0 2)). f_equal.
unfold spZ in Hspe. lia.
- regq4 HS HX' (3%bv:reg) 0%nat. rewrite (HE 3%nat 3%bv eq_refl). exact G3.
- regq4 HS HX' (4%bv:reg) 0%nat. rewrite (HE 4%nat 4%bv eq_refl). exact G4.
- regq4 HS HX' (8%bv:reg) 1%nat. reflexivity.
- regq4 HS HX' (9%bv:reg) 2%nat. reflexivity.
- regq4 HS HX' (18%bv:reg) 3%nat. reflexivity.
- regq4 HS HX' (19%bv:reg) 4%nat. reflexivity.
- regq4 HS HX' (20%bv:reg) 5%nat. reflexivity.
- regq4 HS HX' (21%bv:reg) 6%nat. reflexivity.
- regq4 HS HX' (22%bv:reg) 7%nat. reflexivity.
- regq4 HS HX' (23%bv:reg) 8%nat. reflexivity.
- regq4 HS HX' (24%bv:reg) 9%nat. reflexivity.
- regq4 HS HX' (25%bv:reg) 0%nat. rewrite (HE 25%nat 25%bv eq_refl). exact G25.
- regq4 HS HX' (26%bv:reg) 0%nat. rewrite (HE 26%nat 26%bv eq_refl). exact G26.
- regq4 HS HX' (27%bv:reg) 0%nat. rewrite (HE 27%nat 27%bv eq_refl). exact G27. }
split; [exact Hid|].
split. { regq4 HS HX' (10%bv:reg) 0%nat. rewrite (HE 18%nat 18%bv eq_refl), G18. symmetry. apply Z_to_bv_bv_unsigned. }
split; [| split; [exact HB | split; [apply HQ; intros a Ha; apply mbyte_eq_of1'; lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _) end | exact HRP]]].
cbn [ms_mem mkst].
eapply obj_at_transport_range; [exact HOR | exact (proj1 LAY_Raw_ok) |].
intros i Hi. apply mbyte_eq_of1'.
lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _) end.
Qed.
Lemma ra_st_R :
forall (FP : list (Z * Z)) (Q : Z -> Z -> Prop) (RP : astate -> Prop) cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte) (cur : Z) (r : word),
rcx_pre cx -> ra_origin cx regs0 ->
journal src0_msyms MR RAWADD_STK (spZ regs0) FP L A mem md L1 A1 mem1 md1 ->
st_init_done A1 = true -> RP A1 ->
Permutation (blocks L1 A1) (blocks L A) -> In (c_raw cx, RAW_SIZE) (blocks L A) ->
obj_at src0segs mem1 (c_raw cx) LAY_Raw (rvals' cx cur) ->
frame_savedN src0_msyms 10 regs0 mem1 (spZ regs0) ->
getr regs1 2 = Z_to_bv 64 (c_sp cx) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 25 = getr regs0 25 -> getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
getr regs1 8 = Z_to_bv 64 (c_raw cx) -> getr regs1 18 = r ->
(forall a, c_raw cx + 40 <= a < c_raw cx + 44 -> inFP FP a) -> Q (bv_unsigned r) (bv_unsigned r mod 2 ^ 32) ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_ST) mem1 (seg_rom src0segs)) md1)
(ra_postR API FP Q RP cx L A mem md regs0).
Proof.
intros FP Q RP cx L A mem md L1 A1 md1 regs0 regs1 mem1 cur r Hcx HO HJ Hid HRP HB Hrawin HOR HFS G2 G3 G4 G25 G26 G27 G8 G18 HFPraw HQ.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRSv : RAW_SIZE = 48) by reflexivity.
pose proof Hcx as (Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & _).
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & _).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH1.
assert (Hrawin1 : In (c_raw cx, 48) (blocks L1 A1)).
{ rewrite <- HRSv. eapply Permutation_in; [apply Permutation_sym; exact HB | exact Hrawin]. }
set (sp := c_sp cx) in *.
set (extra := savedN_vals 10 regs0).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 extra) n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX : forall j, (j < 10)%nat -> ew (Ereg regs1 extra) (32 + j)%nat = nth j (savedN_vals 10 regs0) (Z_to_bv 64 0)).
{ intros j Hj. rewrite ew_Ereg_extra. reflexivity. }
assert (HE2 : bv_unsigned (ew (Ereg regs1 extra) 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HE8 : bv_unsigned (ew (Ereg regs1 extra) 8) = c_raw cx) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HS : st_ok src0segs (Ereg regs1 extra) ss_st_c (mkst regs1 (Z_to_bv 64 PC_ST) mem1 (seg_rom src0segs))).
{ change ss_st_c with ss_st. unfold ss_st. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
replace sp with (spZ regs0 - 128) by lia.
apply (saved_chunks_at_ok src0_msyms 10 _ mem1 regs0 (spZ regs0) 128 32 ltac:(lia) HX HFS).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE8.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable src0_msyms).
apply (proj1 (heap_blocks _ _ LAWS L1 A1 mem1 md1 (c_raw cx) 48 o HH1 Hrawin1 ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HE2, HE8. repeat split. lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE2, HE8.
change (2 ^ 4) with 16. repeat split; first [lia | assumption]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_ST) mem1 (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ PC_RET.
{ apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_block; [reflexivity | exact HE8 | exact Hrawin1 | cbn; lia | cbn; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. apply HFPraw. lia. }
pose proof (st_ok_mem_ok _ _ _ _ HS) as Hm. destruct Hm as (_ & Hm & _).
apply Forall_inv_tail in Hm. apply Forall_inv in Hm.
unfold region_ok in Hm. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in Hm. destruct Hm as (_ & _ & _ & Hcs).
apply Forall_inv in Hcs. rewrite HE8 in Hcs.
pose proof (bv_unsigned_in_range 64 r) as Rr. change (bv_modulus 64) with (2 ^ 64) in Rr.
assert (Hcur' : val_mem src0segs (ms_mem ms) (c_raw cx + 40) 4 (bv_unsigned r mod 2 ^ 32)).
{ change (2 ^ 32) with (2 ^ (8 * Z.of_N 4)).
eapply (val_of_chunk_ok_mod _ _ _ 40 4%N); [exact Hcs | | exact Rr | cbn; lia].
cbn [sv_denot]. rewrite (HE 18%nat 18%bv eq_refl), G18, Z.add_0_r. reflexivity. }
assert (HOR' : obj_at src0segs (ms_mem ms) (c_raw cx) LAY_Raw (rvals' cx (bv_unsigned r mod 2 ^ 32))).
{ eapply obj_at_raw_cur; [exact HOR | | exact Hcur' | apply Z.mod_pos_bound; lia].
intros i Hi. apply mbyte_eq_of1'.
lazymatch goal with HF : frame_of _ _ _ _ |- _ => apply HF end.
rewrite unsigned_lit_small by lia.
intros (r0 & Hr0 & Hin0). cbv [In] in Hr0.
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; rewrite ?HE2, ?HE8 in Hin0; lia |]).
destruct Hr0. }
assert (HFS' : frame_savedN src0_msyms 10 regs0 (ms_mem ms) (spZ regs0)).
{ eapply (frame_savedN_kept src0_msyms 10); [lia | exact HFS|]. intros a Ha. apply mbyte_eq_of1'.
lazymatch goal with HF : frame_of _ _ _ _ |- _ => apply HF end.
rewrite unsigned_lit_small by lia.
intros (r0 & Hr0 & Hin0). cbv [In] in Hr0.
repeat (destruct Hr0 as [<- | Hr0]; [cbn [r_base r_wlo r_whi base_val] in Hin0; rewrite ?HE2, ?HE8 in Hin0; lia |]).
destruct Hr0. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [2; 3; 4; 18; 25; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HK.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (ra_ret_R FP Q RP cx L A mem md L1 A1 md1 regs0 (ms_regs ms) (ms_mem ms) (bv_unsigned r mod 2 ^ 32) r Hcx HO HJ Hid HRP HB HOR' HFS');
[ rewrite (HK 2%bv ltac:(cbv; tauto)); exact G2 | rewrite (HK 3%bv ltac:(cbv; tauto)); exact G3
| rewrite (HK 4%bv ltac:(cbv; tauto)); exact G4
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact G25 | rewrite (HK 26%bv ltac:(cbv; tauto)); exact G26 | rewrite (HK 27%bv ltac:(cbv; tauto)); exact G27
| rewrite (HK 18%bv ltac:(cbv; tauto)); exact G18 | exact HQ ].
Qed.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
