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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b
YI06 UI5b YI09 YI08 YI0r YI0o YI6a UI1w UI3p UI3m UI3t.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01 YI0g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI3w UI4j UI4h UI4d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI5d YI5a YI2w UI2v UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ssC2 : sstate :=
ra_ssW PC_C (sr_set sr_atoms 10%bv (SLit 2)) 0 0 [] false
[(18%nat, mkAF 3 9 0); (25%nat, mkAF 4 256 0); (13%nat, mkAF 1 65535 0); (14%nat, mkAF 1 65535 0); (24%nat, mkAF 0 8 0)] [] [].
Definition ssL4X : sstate :=
ra_ssW PC_L4X sr_atoms 0 0 [] false
[(18%nat, mkAF 3 9 0); (25%nat, mkAF 4 256 0); (10%nat, mkAF 1 65535 0); (12%nat, mkAF 1 65535 0); (19%nat, mkAF 4096 CEIL_MAX 4)] [] [].
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Variables (IMGV LCTV : list Z).
Definition at_L1 (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (p icl idl : Z) (b : rbound) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (pint : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 PC_L1) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\   res_ok A2 (rb_acc b 1 (prN (c_nP cx))) /\
Permutation (blocks L2 A2) ((pint, c_nP cx) :: blocks L A) /\
wtok' RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] (blocks L A) (pint, c_nP cx) /\ pint <> 0 /\
ra_regs regs2 cx /\ getr regs2 23 = Z_to_bv 64 (c_slct cx) /\ getr regs2 24 = Z_to_bv 64 p /\ getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) /\
getr regs2 18 = Z_to_bv 64 icl /\ getr regs2 25 = Z_to_bv 64 idl /\
getr regs2 19 = Z_to_bv 64 pint /\ getr regs2 20 = Z_to_bv 64 pint /\ getr regs2 26 = Z_to_bv 64 0 /\
getr regs2 12 = Z_to_bv 64 (c_w cx) /\
objs_at mem2 cx (c_rcur cx) /\ frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) /\
fbC mem2 cx.
Definition at_L4X (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (p icl idl : Z) (b : rbound) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (pint : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 PC_L4X) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\   res_ok A2 (rb_acc b 1 (prN (c_nP cx))) /\
Permutation (blocks L2 A2) ((pint, c_nP cx) :: blocks L A) /\
wtok' RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] (blocks L A) (pint, c_nP cx) /\ pint <> 0 /\
ra_regs regs2 cx /\ getr regs2 23 = Z_to_bv 64 (c_slct cx) /\ getr regs2 24 = Z_to_bv 64 p /\ getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) /\
getr regs2 18 = Z_to_bv 64 icl /\ getr regs2 25 = Z_to_bv 64 idl /\
getr regs2 19 = Z_to_bv 64 pint /\ getr regs2 10 = Z_to_bv 64 (c_h cx) /\ getr regs2 12 = Z_to_bv 64 (c_w cx) /\
objs_at mem2 cx (c_rcur cx) /\ frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) /\
garr8 ubs0segs mem2 pint (YO07.interlace (c_w cx) IMGV) /\ Z.of_nat (length (YO07.interlace (c_w cx) IMGV)) = c_nP cx /\ fbC mem2 cx.
Lemma ra_il1_R :
forall cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte) (p icl idl : Z) (b : rbound),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 ->
st_init_done A1 = true -> res_ok A1 b -> rawadd_room b (c_nP cx) -> Permutation (blocks L1 A1) (blocks L A) -> Permutation (blocks L A) (c_blocks cx) ->
ra_regs regs1 cx -> getr regs1 23 = Z_to_bv 64 (c_slct cx) -> getr regs1 22 = Z_to_bv 64 (c_cfp cx + 30) ->
getr regs1 10 = Z_to_bv 64 2 -> getr regs1 24 = Z_to_bv 64 p -> 0 <= p <= 8 ->
getr regs1 18 = Z_to_bv 64 icl -> getr regs1 25 = Z_to_bv 64 idl -> 3 <= icl <= 9 -> 4 <= idl <= 256 ->
getr regs1 13 = Z_to_bv 64 (c_w cx) -> getr regs1 14 = Z_to_bv 64 (c_h cx) ->
objs_at mem1 cx (c_rcur cx) -> frame_savedN ubs0_msyms 12 regs0 mem1 (spZ regs0) ->
fbC mem1 cx ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_C) mem1 (seg_rom ubs0segs)) md1)
(at_L1 cx L A mem md regs0 p icl idl b).
Proof using IMG.
intros cx L A mem md L1 A1 md1 regs0 regs1 mem1 p icl idl b Hcx HO HJ Hid HRq HRM HB1 HB HR G23 G22 G10 G24 Hp G18 G25 Hicl Hidl G13 G14 Hobjs HFS HFBC.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof (objs_fields_ok _ _ _ Hobjs) as HFO.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof HFO as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof HJ as (HH1 & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
assert (Hrawin : In (c_raw cx, RAW_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hgin : In (c_g cx, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
assert (Hrawin1 : In (c_raw cx, 48) (blocks L1 A1)) by (rewrite <- HRSv; eapply Permutation_in; [apply Permutation_sym; exact HB1 | exact Hrawin]).
assert (Hgin1 : In (c_g cx, 96) (blocks L1 A1)) by (rewrite <- HGSv; eapply Permutation_in; [apply Permutation_sym; exact HB1 | exact Hgin]).
assert (HnP1 : 1 <= c_w cx * c_h cx) by nia. assert (HnPlo : 1 <= c_nP cx <= 100000000) by (unfold c_nP; nia).
remember (Ereg regs1 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs1 cx (c_rcur cx) []) as HX. pose proof (E_rv regs1 cx (c_rcur cx) []) as HY. rewrite <- HE0 in HX, HY.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE18 : ew E 18 = Z_to_bv 64 icl) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE25 : ew E 25 = Z_to_bv 64 idl) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (HE13 : ew E 13 = Z_to_bv 64 (c_w cx)) by (rewrite (HE 13%nat 13%bv eq_refl); exact G13).
assert (HE14 : ew E 14 = Z_to_bv 64 (c_h cx)) by (rewrite (HE 14%nat 14%bv eq_refl); exact G14).
assert (HE24 : ew E 24 = Z_to_bv 64 p) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE35 : ew E 35 = Z_to_bv 64 (c_w cx)) by (apply (HX 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 (c_h cx)) by (apply (HX 4%nat); reflexivity).
assert (HS : st_ok ubs0segs E ssC2 (mkst regs1 (Z_to_bv 64 PC_C) mem1 (seg_rom ubs0segs))).
{ subst E. unfold ssC2.
apply (ra_st_okW cx (c_rcur cx) regs1 [] mem1 PC_C _ 0 0 false [] _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact G10].
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE18, HE25, HE13, HE14, HE24, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_C) mem1 (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc; [eapply ra_wr_okW; [exact HE2 | lia | lia | intros X; lia | left; cbn; lia]|].
pose proof (st_ok_reg _ _ _ _ (10%bv:reg) HS) as M10. eval_sr_get_in M10. rewrite denot_lit_U in M10.
rewrite (U_mul_small _ _ _ (c_h cx) (c_w cx) (U_atom _ 14 _ HE14 ltac:(lia)) (U_atom _ 13 _ HE13 ltac:(lia))) in M10 by lia.
replace (c_h cx * c_w cx) with (c_nP cx) in M10 by (unfold c_nP; lia).
jreg HS (2%bv:reg) as M2. rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2 in M2.
jreg HS (4%bv:reg) as M4. rewrite (HE 4%nat 4%bv eq_refl), R4, Htpv in M4. jreg HS (1%bv:reg) as M1.
assert (Hobjs' : objs_at (ms_mem ms) cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs | | |]; intros k Hk; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (HFS' : frame_savedN ubs0_msyms 12 regs0 (ms_mem ms) (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]. intros a Ha. mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (HFBC' : fbC (ms_mem ms) cx).
{ eapply fbC_kept; [exact HFBC | |]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := c_nP cx) (spc := c_sp cx);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid | exact M10 | exact HRq | apply (rawadd_room_il b (c_nP cx)); [exact HnPlo | exact HRM]
| exact M2 | lia | exact Hspal | lia | lia | exact M4 | exact M1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & Hres & Hkeep & Hhi & HRq2).
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep, Hhi.
assert (Hobjs2 : objs_at mem2 cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs' | | |]; intros k Hk.
- apply (proj1 (Hhi (c_cfp cx + k) ltac:(lia) ltac:(lia))).
- apply (Hkeep _ _ k Hrawin1). lia.
- apply (Hkeep _ _ k Hgin1). lia. }
assert (HFS2 : frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS'|]. intros a Ha. apply (proj1 (Hhi a ltac:(lia) ltac:(lia))). }
assert (HFBC2 : fbC mem2 cx).
{ eapply fbC_kept; [exact HFBC' | |]; intros a Ha; apply (proj1 (Hhi a ltac:(lia) ltac:(lia))). }
jafter_call2 HS 69%nat regs2 mem2 HP2 0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKr : P); [|specialize (HS2 HKr); clear HKr] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HE2 | exact Hhi | lia | lia | cbn; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 9); [rewrite HE9; apply unsigned_lit_small; lia | exact Hhi | lia | lia | cbn; lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro ubs0segs _ _ _ 8); [rewrite HE8; apply unsigned_lit_small; lia | exact Hrawin1 | exact Hkeep | cbn; lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro ubs0segs _ _ _ 44); [rewrite HE44; apply unsigned_lit_small; lia | exact Hgin1 | exact Hkeep | cbn; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (1%bv:reg) as Hpc1. cbn [ms_regs mkst] in Hpc1.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (RA0 + 0x224)) mem2 (seg_rom ubs0segs))) in HJ2.
pose proof HJ2 as (HH2 & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw2) & _). cbn beta in Hstw2.
destruct Hres as (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr).
-
assert (Hbin2 : In (res, c_nP cx) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 res (c_nP cx) HH2 Hbin2 ltac:(unfold c_nP; lia)) as (Hb0 & Hb1 & _).
jreg HS (10%bv:reg) as P10. cbn [ms_regs mkst] in P10. rewrite Hres10 in P10. symmetry in P10.
add_fact' HS 73%nat (mkAF 4096 CEIL_MAX 4). 2:{ rewrite P10, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_L1.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [2; 3; 4; 8; 9; 18; 22; 23; 24; 25; 27]%bv HS ltac:(apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]) ltac:(vm_compute; reflexivity)) as HK3.
cbn [ms_regs mkst] in HK3.
jreg HS (19%bv:reg) as Q19. cbn [ms_regs mkst] in Q19. rewrite P10 in Q19.
jreg HS (20%bv:reg) as Q20. cbn [ms_regs mkst] in Q20. rewrite P10 in Q20.
jreg HS (26%bv:reg) as Q26. cbn [ms_regs mkst] in Q26.
jreg HS (12%bv:reg) as Q12. cbn [ms_regs mkst] in Q12. repeat (rewrite ew_havoc_old in Q12 by (cbv; lia)). rewrite HE35 in Q12.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ3 : forall a, ~ (c_sp cx - 16 <= a < c_sp cx + 48) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msF) a = mbyte ubs0segs mem2 a).
{ intros a Hna Ha. mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
exists L2, A2, (ms_regs msF), (ms_mem msF), md2, res.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [apply ra_rb_il_malloc; [unfold c_nP; lia | exact HRq2]|].
split. { rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc. exact HB1. }
split; [exact Hwr|]. split; [exact Hnz|].
split. { unfold ra_regs. rewrite !HK3 by (cbv; tauto). exact HR. }
split; [rewrite HK3 by (cbv; tauto); exact G23|].
split; [rewrite HK3 by (cbv; tauto); exact G24|].
split; [rewrite HK3 by (cbv; tauto); exact G22|].
split; [rewrite HK3 by (cbv; tauto); exact G18|].
split; [rewrite HK3 by (cbv; tauto); exact G25|].
split; [exact Q19|]. split; [exact Q20|]. split; [exact Q26|]. split; [exact Q12|].
split. { eapply objs_at_kept; [exact Hobjs2 | | |]; intros k Hk; apply MEQ3; lia. }
split. { eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS2|]. intros a Ha. apply MEQ3; lia. }
eapply fbC_kept; [exact HFBC2 | |]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H).
Qed.
Lemma ra_il3_R : lzw_specX API ->
forall cx L A mem md L2 A2 md2 (regs0 regs2 : bvmap 5 word) (mem2 : word -> option byte) (p icl idl pint : Z) (b : rbound),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L2 A2 mem2 md2 ->
st_init_done A2 = true -> res_ok A2 (rb_acc b 1 (prN (c_nP cx))) -> rawadd_room b (c_nP cx) ->
Permutation (blocks L2 A2) ((pint, c_nP cx) :: blocks L A) -> Permutation (blocks L A) (c_blocks cx) ->
wtok' RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] (blocks L A) (pint, c_nP cx) -> pint <> 0 ->
ra_regs regs2 cx -> getr regs2 23 = Z_to_bv 64 (c_slct cx) -> getr regs2 24 = Z_to_bv 64 p -> getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) ->
getr regs2 18 = Z_to_bv 64 icl -> getr regs2 25 = Z_to_bv 64 idl ->
getr regs2 19 = Z_to_bv 64 pint -> getr regs2 10 = Z_to_bv 64 (c_h cx) -> getr regs2 12 = Z_to_bv 64 (c_w cx) ->
3 <= icl <= 9 -> 4 <= idl <= 256 -> 0 <= p <= 8 ->
objs_at mem2 cx (c_rcur cx) -> frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) ->
(c_rcur cx = 0 \/ c_rcur cx = 6) -> Z.land (c_fattr cx) 2 <> 0 -> icl = ra_iclen cx -> idl = 2 ^ (icl - 1) ->
garr8 ubs0segs mem2 pint (YO07.interlace (c_w cx) IMGV) -> Z.of_nat (length (YO07.interlace (c_w cx) IMGV)) = c_nP cx -> fbC mem2 cx ->
SR ubs0segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_L4X) mem2 (seg_rom ubs0segs)) md2)
(fun c' => ra_postR API [(c_raw cx + 40, c_raw cx + 44)] (ra_exitX cx IMGV LCTV) (fun s => res_ok s (rawadd_rb b)) cx L A mem md regs0 c' \/ at_OK API IMGV cx L A mem md regs0 p b c').
Proof using IMG.
intros LZW cx L A mem md L1 A1 md1 regs0 regs1 mem1 p icl idl pint b Hcx HO HJ Hid HRq HRM HB1 HB Hwt Hpnz HR G23 G24 G22 G18 G25 G19 G10 G12 Hicl Hidl Hp Hobjs HFS Hrc Hl2 Hiclv Hidlv HPIX0 HPIXlen HFBC.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity. assert (HLSv : UI3p.LZW_STK = 8400) by reflexivity.
assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof (objs_fields_ok _ _ _ Hobjs) as HFO.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof HFO as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof HJ as (HH1 & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
assert (Hrawin : In (c_raw cx, RAW_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hgin : In (c_g cx, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
assert (Hrawin1 : In (c_raw cx, 48) (blocks L1 A1)) by (rewrite <- HRSv; eapply Permutation_in; [apply Permutation_sym; exact HB1 | right; exact Hrawin]).
assert (Hgin1 : In (c_g cx, 96) (blocks L1 A1)) by (rewrite <- HGSv; eapply Permutation_in; [apply Permutation_sym; exact HB1 | right; exact Hgin]).
assert (Hpin1 : In (pint, c_nP cx) (blocks L1 A1)) by (eapply Permutation_in; [apply Permutation_sym; exact HB1 | left; reflexivity]).
assert (HnP1 : 1 <= c_w cx * c_h cx) by nia. assert (HnPlo : 1 <= c_nP cx <= 100000000) by (unfold c_nP; nia).
destruct (heap_blocks_range _ _ LAWS L1 A1 mem1 md1 pint (c_nP cx) HH1 Hpin1 ltac:(lia)) as (Hb0 & Hb1 & _).
remember (Ereg regs1 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs1 cx (c_rcur cx) []) as HX. pose proof (E_rv regs1 cx (c_rcur cx) []) as HY. rewrite <- HE0 in HX, HY.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE18 : ew E 18 = Z_to_bv 64 icl) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE19 : ew E 19 = Z_to_bv 64 pint) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE10 : ew E 10 = Z_to_bv 64 (c_h cx)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE12 : ew E 12 = Z_to_bv 64 (c_w cx)) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (HE25 : ew E 25 = Z_to_bv 64 idl) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (HS : st_ok ubs0segs E ssL4X (mkst regs1 (Z_to_bv 64 PC_L4X) mem1 (seg_rom ubs0segs))).
{ subst E. unfold ssL4X.
apply (ra_st_okW cx (c_rcur cx) regs1 [] mem1 PC_L4X _ 0 0 false _ _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_Ereg.
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2]. rewrite HE18, HE25, HE10, HE12, HE19, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
destruct (heap_blocks_range _ _ LAWS L1 A1 mem1 md1 pint (c_nP cx) HH1 Hpin1 ltac:(lia)) as (_ & _ & H16).
repeat split; first [lia | exact H16].
- constructor.
- constructor. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_L4X) mem1 (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_LZW_GenerateStream; [eapply ra_wr_okW; [exact HE2 | lia | lia | intros X; lia | left; cbn; lia]|].
jreg HS (10%bv:reg) as A10. cbn [sv_denot] in A10. rewrite HE2 in A10.
pose proof (st_ok_reg _ _ _ _ (11%bv:reg) HS) as A11. eval_sr_get_in A11. rewrite denot_lit_U in A11.
rewrite (U_mulw_small _ _ _ (c_h cx) (c_w cx) (U_atom _ 10 _ HE10 ltac:(lia)) (U_atom _ 12 _ HE12 ltac:(lia))) in A11 by lia.
replace (c_h cx * c_w cx) with (c_nP cx) in A11 by (unfold c_nP; lia).
jreg HS (12%bv:reg) as A12. rewrite HE19 in A12.
jreg HS (13%bv:reg) as A13. rewrite HE25 in A13.
jreg HS (14%bv:reg) as A14. rewrite HE18 in A14.
jreg HS (1%bv:reg) as Ara. jreg HS (2%bv:reg) as Asp. rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2 in Asp.
jreg HS (4%bv:reg) as A4. rewrite (HE 4%nat 4%bv eq_refl), R4, Htpv in A4.
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [3; 8; 9; 19; 22; 23; 24]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
assert (MEQ : forall a, ~ (c_sp cx - 16 <= a < c_sp cx + 48) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs mem1 a).
{ intros a Hna Ha. mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (Hobjs' : objs_at (ms_mem ms) cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; apply MEQ; lia. }
assert (HFS' : frame_savedN ubs0_msyms 12 regs0 (ms_mem ms) (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]. intros a Ha. apply MEQ; lia. }
assert (HFBC' : fbC (ms_mem ms) cx).
{ eapply fbC_kept; [exact HFBC | |]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (HPIXc : garr8 ubs0segs (ms_mem ms) pint (YO07.interlace (c_w cx) IMGV)).
{ apply (garr8_frame ubs0segs mem1 (ms_mem ms) pint _ HPIX0). rewrite HPIXlen. intros a Ha. apply MEQ; lia. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
assert (Hsp_l : spZ (ms_regs ms) = c_sp cx) by (unfold spZ; rewrite Asp; apply unsigned_lit_small; lia).
eapply SR_bind.
{ unfold lzw_specX in LZW.
eapply (LZW RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 (ms_mem ms) md1 (ms_regs ms)
(c_sp cx + 8) (c_nP cx) pint idl icl pint (c_nP cx) (YO07.interlace (c_w cx) IMGV) (rb_acc b 1 (prN (c_nP cx))));
rewrite ?Hsp_l; try first [exact HJ | exact Hid | exact A10 | exact A11 | exact A12 | exact A13 | exact A14 | exact A4 | exact Hpin1 | exact HPIXc | exact HRq].
- rewrite Ara. apply ret_ok_even. vm_compute. reflexivity.
- exact Hspal.
- lia.
- lia.
- lia.
- replace (c_sp cx + 8) with (c_sp cx + 1 * 8) by lia. rewrite Z.mod_add by lia.
rewrite (Znumtheory.Zmod_div_mod 8 16 (c_sp cx)); [rewrite Hspal; reflexivity | lia | lia | exists 2; reflexivity].
- lia.
- lia.
- lia.
- lia.
- lia.
- eapply (rodata_ok_of_heap API IMG). exact (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
- rewrite <- HPIXlen, Nat2Z.id. reflexivity.
-   apply rawadd_room_lzw1; [unfold c_nP; lia | exact HRM]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & MHI & MBL & Hcase).
rewrite Hsp_l in MHI. rewrite Ara.
jafter_call_keep HS 71%nat regs2 mem2 HP2 [1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKr : P); [|specialize (HS2 HKr); clear HKr] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_pointwise ubs0segs _ _ _ 9); [rewrite HE9; apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. apply MHI; lia.
- eapply (region_kept_block_ro ubs0segs _ _ _ 8); [rewrite HE8; apply unsigned_lit_small; lia | exact Hrawin1 | exact MBL | cbn; lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro ubs0segs _ _ _ 44); [rewrite HE44; apply unsigned_lit_small; lia | exact Hgin1 | exact MBL | cbn; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (Hobjs2 : objs_at mem2 cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs' | | |]; intros i Hi.
- apply MHI; lia.
- apply (MBL _ _ i Hrawin1). lia.
- apply (MBL _ _ i Hgin1). lia. }
assert (HFS2 : frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS'|]. intros a Ha. apply MHI; lia. }
assert (HFBC2 : fbC mem2 cx).
{ eapply fbC_kept; [exact HFBC' | |]; intros a Ha; apply MHI; lia. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (RA0 + 0x40c)) mem2 (seg_rom ubs0segs))) in HJ2.
pose proof HJ2 as (HH2 & _ & _ & _ & _ & _ & _).
destruct Hcase as [(-> & bb & Lbb & M & HB2 & Hw & W1 & W2 & HM & HM2 & HVOK & HRo) | (Hres & HB2 & HpR & HVNONE & HRo)].
-
pin_reg' HS (10%bv:reg) 0 Hres10.
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_free.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as K10. cbn [ms_regs mkst] in K10. repeat (rewrite ew_havoc_old in K10 by (cbv; lia)). rewrite HE19 in K10.
jreg HS (2%bv:reg) as K2. cbn [ms_regs mkst] in K2. repeat (rewrite ew_havoc_old in K2 by (cbv; lia)). rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2 in K2.
jreg HS (4%bv:reg) as K4. cbn [ms_regs mkst] in K4. repeat (rewrite ew_havoc_old in K4 by (cbv; lia)). rewrite (HE 4%nat 4%bv eq_refl), R4, Htpv in K4.
jreg HS (1%bv:reg) as K1. cbn [ms_regs mkst] in K1.
assert (Hpin2 : In (pint, c_nP cx) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact Hpin1]).
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msA end.
assert (MEQA : forall x : word, ms_mem msA x = mem2 x).
{ intros x. lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) x) end. }
eapply SR_bind.
{ eapply (jfree_tok_res API IMG) with (a := pint) (n := c_nP cx) (spc := c_sp cx);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Hid2 | | exact HRo | exact K10 | exact K2 | lia | exact Hspal | lia | lia | exact K4 | exact K1 | apply ret_ok_even; vm_compute; reflexivity ].
split; [exact Hpin2|]. eapply ftok_of_wtok; [exact Hwt | lia | lia]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & Hid3 & HP3 & Hrm & Hkeep3 & Hhi3 & HRq3).
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, Hrm.
assert (HB3 : Permutation (blocks L3 A3) ((bb, Lbb) :: blocks L A)).
{ eapply perm_after_rm1; [|exact Hrm]. eapply Permutation_trans; [exact HB2|].
eapply Permutation_trans; [apply perm_skip; exact HB1|]. apply perm_swap. }
assert (Hrawin3 : In (c_raw cx, 48) (blocks L3 A3)) by (eapply Permutation_in; [apply Permutation_sym; exact HB3 | right; rewrite <- HRSv; exact Hrawin]).
assert (Hgin3 : In (c_g cx, 96) (blocks L3 A3)) by (eapply Permutation_in; [apply Permutation_sym; exact HB3 | right; rewrite <- HGSv; exact Hgin]).
jafter_call_keep HS 87%nat regs3 mem3 HP3 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKr : P); [|specialize (HS2 HKr); clear HKr] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 9) with (xlo := c_sp cx - 8192) (xhi := c_sp cx);
[repeat (rewrite ew_havoc_old by (cbv; lia)); rewrite HE9; apply unsigned_lit_small; lia | | cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia].
intros x Hx Hnx. apply Hhi3; lia.
- eapply (region_kept_block_ro ubs0segs _ _ _ 8); [repeat (rewrite ew_havoc_old by (cbv; lia)); rewrite HE8; apply unsigned_lit_small; lia | exact Hrawin3 | | cbn; lia | cbn; lia | cbn; lia].
intros b' m' i Hb' Hi. exact (Hkeep3 b' m' i Hb' Hi).
- eapply (region_kept_block_ro ubs0segs _ _ _ 44); [repeat (rewrite ew_havoc_old by (cbv; lia)); rewrite HE44; apply unsigned_lit_small; lia | exact Hgin3 | | cbn; lia | cbn; lia | cbn; lia].
intros b' m' i Hb' Hi. exact (Hkeep3 b' m' i Hb' Hi). }
clear HS. rename HS2 into HS.
assert (MHI3 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (c_sp cx - 8192 <= a < c_sp cx) -> mbyte ubs0segs mem3 a = mbyte ubs0segs mem2 a).
{ intros a Ha Hna. rewrite (proj1 (Hhi3 a Ha Hna)). unfold mbyte. rewrite MEQA. reflexivity. }
assert (Hobjs3 : objs_at mem3 cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs2 | | |]; intros i Hi.
- apply MHI3; lia.
- etransitivity; [apply (Hkeep3 _ _ i Hrawin3); lia | unfold mbyte; rewrite MEQA; reflexivity].
- etransitivity; [apply (Hkeep3 _ _ i Hgin3); lia | unfold mbyte; rewrite MEQA; reflexivity]. }
assert (HFS3 : frame_savedN ubs0_msyms 12 regs0 mem3 (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS2|]. intros a Ha. apply MHI3; lia. }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (RA0 + 0x418)) mem3 (seg_rom ubs0segs))) in HJ3.
jrun_to LAWS ubs0tbl_ok HS HJ3 PC_OK.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret. right.
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [2; 3; 4; 8; 9; 22; 23; 24; 27]%bv HS
ltac:(apply env_agree_havoc_ge; [cbv; lia | apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]]) ltac:(vm_compute; reflexivity)) as HK3.
cbn [ms_regs mkst] in HK3.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msF) a = mbyte ubs0segs mem3 a).
{ intros a Ha. apply mbyte_eq_of1'. lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _) end. }
exists L3, A3, (ms_regs msF), (ms_mem msF), md3, bb, Lbb, M.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hid3|].
split; [apply (ra_rb_il b _ (c_nP cx) Lbb); [unfold c_nP; lia | lia | exact HRq3]|].
split. { unfold ra_regs. rewrite !HK3 by (cbv; tauto). exact HR. }
split; [rewrite HK3 by (cbv; tauto); exact G23|].
split; [rewrite HK3 by (cbv; tauto); exact G24|].
split; [rewrite HK3 by (cbv; tauto); exact G22|].
split; [exact HB3|].
split; [exact Hw|].
split. { intros k Hk. rewrite MEQ3, MHI3 by lia. apply W1. exact Hk. }
split. { intros k Hk. rewrite MEQ3, MHI3 by lia. replace (c_sp cx + 16) with (c_sp cx + 8 + 8) by lia. apply W2. exact Hk. }
split; [exact HM|].
split. { eapply objs_at_kept; [exact Hobjs3 | | |]; intros i Hi; apply MEQ3; lia. }
split. { eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS3|]. intros a Ha. apply MEQ3; lia. }
assert (Hbbin3 : In (bb, Lbb) (blocks L3 A3)) by (eapply Permutation_in; [apply Permutation_sym; exact HB3 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L3 A3 _ _ bb Lbb (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) Hbbin3 ltac:(lia)) as (Hbb0 & Hbb1 & _).
assert (Hbbin2 : In (bb, Lbb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
replace (ra_iclen cx) with icl by exact Hiclv. rewrite <- Hidlv.
replace (ra_pix cx IMGV) with (YO07.interlace (c_w cx) IMGV) by (unfold ra_pix, YO07.flag; destruct (Z.eqb_spec (Z.land (c_fattr cx) 2) 0); [lia | reflexivity]).
split; [| split; [exact HM2|]].
{ destruct HVOK as (out & Hout & HGout & HMout). exists out. split; [exact Hout|]. split; [| exact HMout].
apply (garr8_frame ubs0segs mem2 (ms_mem msF) bb out HGout). intros a Ha. rewrite <- HMout in Ha. rewrite MEQ3 by lia.
replace a with (bb + (a - bb)) by lia. etransitivity; [apply (Hkeep3 _ _ (a - bb) Hbbin3); lia | unfold mbyte; rewrite MEQA; reflexivity]. }
eapply fbC_kept; [exact HFBC2 | |]; intros a Ha; rewrite MEQ3, MHI3 by lia; reflexivity.
-
jreg HS (10%bv:reg) as P10. cbn [ms_regs mkst] in P10. rewrite Hres10 in P10. symmetry in P10.
add_fact' HS 75%nat (mkAF 2 5 0). 2:{ rewrite P10, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_free.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as K10. cbn [ms_regs mkst] in K10. repeat (rewrite ew_havoc_old in K10 by (cbv; lia)). rewrite HE19 in K10.
jreg HS (2%bv:reg) as K2. cbn [ms_regs mkst] in K2. repeat (rewrite ew_havoc_old in K2 by (cbv; lia)). rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2 in K2.
jreg HS (4%bv:reg) as K4. cbn [ms_regs mkst] in K4. repeat (rewrite ew_havoc_old in K4 by (cbv; lia)). rewrite (HE 4%nat 4%bv eq_refl), R4, Htpv in K4.
jreg HS (1%bv:reg) as K1. cbn [ms_regs mkst] in K1.
assert (Hpin2 : In (pint, c_nP cx) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | exact Hpin1]).
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msA end.
assert (MEQA : forall x : word, ms_mem msA x = mem2 x).
{ intros x. lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) x) end. }
eapply SR_bind.
{ eapply (jfree_tok_res API IMG) with (a := pint) (n := c_nP cx) (spc := c_sp cx);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Hid2 | | exact HRo | exact K10 | exact K2 | lia | exact Hspal | lia | lia | exact K4 | exact K1 | apply ret_ok_even; vm_compute; reflexivity ].
split; [exact Hpin2|]. eapply ftok_of_wtok; [exact Hwt | lia | lia]. }
cbv beta. intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & Hid3 & HP3 & Hrm & Hkeep3 & Hhi3 & HRq3).
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, Hrm.
assert (HB3 : Permutation (blocks L3 A3) (blocks L A)).
{ eapply perm_after_rm1; [|exact Hrm]. eapply Permutation_trans; [exact HB2 | exact HB1]. }
assert (Hrawin3 : In (c_raw cx, 48) (blocks L3 A3)) by (eapply Permutation_in; [apply Permutation_sym; exact HB3 | rewrite <- HRSv; exact Hrawin]).
assert (Hgin3 : In (c_g cx, 96) (blocks L3 A3)) by (eapply Permutation_in; [apply Permutation_sym; exact HB3 | rewrite <- HGSv; exact Hgin]).
jafter_call_keep HS 87%nat regs3 mem3 HP3 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKr : P); [|specialize (HS2 HKr); clear HKr] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 9) with (xlo := c_sp cx - 8192) (xhi := c_sp cx);
[repeat (rewrite ew_havoc_old by (cbv; lia)); rewrite HE9; apply unsigned_lit_small; lia | | cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia].
intros x Hx Hnx. apply Hhi3; lia.
- eapply (region_kept_block_ro ubs0segs _ _ _ 8); [repeat (rewrite ew_havoc_old by (cbv; lia)); rewrite HE8; apply unsigned_lit_small; lia | exact Hrawin3 | | cbn; lia | cbn; lia | cbn; lia].
intros b' m' i Hb' Hi. exact (Hkeep3 b' m' i Hb' Hi).
- eapply (region_kept_block_ro ubs0segs _ _ _ 44); [repeat (rewrite ew_havoc_old by (cbv; lia)); rewrite HE44; apply unsigned_lit_small; lia | exact Hgin3 | | cbn; lia | cbn; lia | cbn; lia].
intros b' m' i Hb' Hi. exact (Hkeep3 b' m' i Hb' Hi). }
clear HS. rename HS2 into HS.
assert (MHI3 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (c_sp cx - 8192 <= a < c_sp cx) -> mbyte ubs0segs mem3 a = mbyte ubs0segs mem2 a).
{ intros a Ha Hna. rewrite (proj1 (Hhi3 a Ha Hna)). unfold mbyte. rewrite MEQA. reflexivity. }
assert (Hobjs3 : objs_at mem3 cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs2 | | |]; intros i Hi.
- apply MHI3; lia.
- etransitivity; [apply (Hkeep3 _ _ i Hrawin3); lia | unfold mbyte; rewrite MEQA; reflexivity].
- etransitivity; [apply (Hkeep3 _ _ i Hgin3); lia | unfold mbyte; rewrite MEQA; reflexivity]. }
assert (HFS3 : frame_savedN ubs0_msyms 12 regs0 mem3 (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS2|]. intros a Ha. apply MHI3; lia. }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (RA0 + 0x418)) mem3 (seg_rom ubs0segs))) in HJ3.
jrun_to LAWS ubs0tbl_ok HS HJ3 PC_ST.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [2; 3; 4; 8; 27]%bv HS
ltac:(apply env_agree_havoc_ge; [cbv; lia | apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]]) ltac:(vm_compute; reflexivity)) as HK3.
cbn [ms_regs mkst] in HK3.
jreg HS (18%bv:reg) as Q18. cbn [ms_regs mkst] in Q18.
lazymatch type of HS with st_ok _ _ _ ?msf => rename msf into msF end.
assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msF) a = mbyte ubs0segs mem3 a).
{ intros a Ha. apply mbyte_eq_of1'. lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _) end. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono; [| cbv beta; intros c' Hc'; left; exact Hc'].
eapply (ra_st_R API IMG [(c_raw cx + 40, c_raw cx + 44)] (ra_exitX cx IMGV LCTV) (fun s => res_ok s (rawadd_rb b)) cx L A mem md L3 A3 md3 regs0 (ms_regs msF) (ms_mem msF) (c_rcur cx));
[ exact (proj1 Hcx) | exact HO | exact HJ3 | exact Hid3 | apply (ra_rb_il_eidx b _ (c_nP cx)); [unfold c_nP; lia | exact HRq3] | exact HB3 | exact Hrawin | | | | | | | | exact Q18
| intros a Ha; exists (c_raw cx + 40, c_raw cx + 44); split; [left; reflexivity | cbn; lia]
| rewrite P10, unsigned_lit_small by lia; rewrite Hres;
exists 5; rewrite (ra_model_lzw cx IMGV LCTV Hrc (proj2 Hcx));
replace (ra_iclen cx) with icl by exact Hiclv; rewrite <- Hidlv;
replace (ra_pix cx IMGV) with (YO07.interlace (c_w cx) IMGV) by (unfold ra_pix, YO07.flag; destruct (Z.eqb_spec (Z.land (c_fattr cx) 2) 0); [lia | reflexivity]);
unfold lzw_vnone in HVNONE; rewrite HVNONE; split; [reflexivity | split; reflexivity] ]; cbn [ms_regs ms_mem].
+ eapply obj_at_transport_range; [exact (proj1 (proj2 Hobjs3)) | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply MEQ3. lia.
+ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS3|]. intros a Ha. apply MEQ3; lia.
+ rewrite HK3 by (cbv; tauto). exact R2.
+ rewrite HK3 by (cbv; tauto). rewrite R3, Hgp0. reflexivity.
+ rewrite HK3 by (cbv; tauto). rewrite R4, Htp0. reflexivity.
+ rewrite HK3 by (cbv; tauto). rewrite R27, H27o. reflexivity.
+ rewrite HK3 by (cbv; tauto). exact R8.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
