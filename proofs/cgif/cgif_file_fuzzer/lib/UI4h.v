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
YI06 UI5b YI09 YI08 YI0r YI0o UI1w UI3p UI3m UI3t
UI3w UI4j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI5d YI5a YI2w UI2v UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ssC0 : sstate :=
ra_ssW PC_C (sr_set sr_atoms 10%bv (SLit 0)) 0 0 [] false
[(18%nat, mkAF 3 9 0); (25%nat, mkAF 4 256 0); (13%nat, mkAF 1 65535 0); (14%nat, mkAF 1 65535 0)] [] [].
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Variables (IMGV LCTV : list Z).
Definition at_OK (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (p : Z) (b : rbound) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (bb Lbb M : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 PC_OK) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\   ra_rb b A2 Lbb /\
ra_regs regs2 cx /\ getr regs2 23 = Z_to_bv 64 (c_slct cx) /\ getr regs2 24 = Z_to_bv 64 p /\ getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) /\
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) /\
wtok' RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] (blocks L A) (bb, Lbb) /\
word_mem ubs0segs mem2 (c_sp cx + 8) bb /\ val_mem ubs0segs mem2 (c_sp cx + 16) 4 M /\ 1 <= M <= Lbb /\
objs_at mem2 cx (c_rcur cx) /\ frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) /\
lzw_vok (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) mem2 bb M /\ M <= 2 * c_nP cx + 16 /\
fbC mem2 cx.
Lemma rodata_ok_of_heap : forall L1 A1 m1 md1, heap_ok MR L1 A1 m1 md1 -> lzw_rodata_ok m1.
Proof using IMG.
intros L1 A1 m1 md1 HH i Hi. apply (il_rodata IMG L1 A1 m1 md1 _ (proj1 HH)).
change (ms_debruijn ubs0_msyms) with ubs0_D_debruijn32. unfold ubs0_D_debruijn32, ubs0_D_const_u64_0x0101010101010102. lia.
Qed.
Lemma ra_plain_R : lzw_specX API ->
forall cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte) (p icl idl : Z) (b : rbound),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 ->
st_init_done A1 = true -> res_ok A1 b -> rawadd_room b (c_nP cx) -> Permutation (blocks L1 A1) (blocks L A) -> Permutation (blocks L A) (c_blocks cx) ->
ra_regs regs1 cx -> getr regs1 23 = Z_to_bv 64 (c_slct cx) -> getr regs1 22 = Z_to_bv 64 (c_cfp cx + 30) ->
getr regs1 10 = Z_to_bv 64 0 -> getr regs1 24 = Z_to_bv 64 p ->
getr regs1 18 = Z_to_bv 64 icl -> getr regs1 25 = Z_to_bv 64 idl -> 3 <= icl <= 9 -> 4 <= idl <= 256 ->
getr regs1 13 = Z_to_bv 64 (c_w cx) -> getr regs1 14 = Z_to_bv 64 (c_h cx) ->
objs_at mem1 cx (c_rcur cx) -> frame_savedN ubs0_msyms 12 regs0 mem1 (spZ regs0) ->
(c_rcur cx = 0 \/ c_rcur cx = 6) -> Z.land (c_fattr cx) 2 = 0 -> icl = ra_iclen cx -> idl = 2 ^ (icl - 1) ->
garr8 ubs0segs mem (c_img cx) IMGV -> Z.of_nat (length IMGV) = c_nP cx -> fbC mem1 cx ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_C) mem1 (seg_rom ubs0segs)) md1)
(fun c' => ra_postR API [(c_raw cx + 40, c_raw cx + 44)] (ra_exitX cx IMGV LCTV) (fun s => res_ok s (rawadd_rb b)) cx L A mem md regs0 c' \/ at_OK cx L A mem md regs0 p b c').
Proof using IMG.
intros LZW cx L A mem md L1 A1 md1 regs0 regs1 mem1 p icl idl b Hcx HO HJ Hid HRq HRM HB1 HB HR G23 G22 G10 G24 G18 G25 Hicl Hidl G13 G14 Hobjs HFS Hrc Hl0 Hiclv Hidlv HIMG0 HIMGlen HFBC.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity. assert (HLSv : UI3p.LZW_STK = 8400) by reflexivity.
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
assert (Himgin : In (c_img cx, c_Nimg cx) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; right; left; reflexivity]).
assert (Hrawin1 : In (c_raw cx, 48) (blocks L1 A1)) by (rewrite <- HRSv; eapply Permutation_in; [apply Permutation_sym; exact HB1 | exact Hrawin]).
assert (Hgin1 : In (c_g cx, 96) (blocks L1 A1)) by (rewrite <- HGSv; eapply Permutation_in; [apply Permutation_sym; exact HB1 | exact Hgin]).
assert (Himgin1 : In (c_img cx, c_Nimg cx) (blocks L1 A1)) by (eapply Permutation_in; [apply Permutation_sym; exact HB1 | exact Himgin]).
assert (HnP1 : 1 <= c_w cx * c_h cx) by nia.
remember (Ereg regs1 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs1 cx (c_rcur cx) []) as HX. pose proof (E_rv regs1 cx (c_rcur cx) []) as HY. rewrite <- HE0 in HX, HY.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE23 : ew E 23 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE24 : ew E 24 = Z_to_bv 64 p) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE18 : ew E 18 = Z_to_bv 64 icl) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE25 : ew E 25 = Z_to_bv 64 idl) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (HE13 : ew E 13 = Z_to_bv 64 (c_w cx)) by (rewrite (HE 13%nat 13%bv eq_refl); exact G13).
assert (HE14 : ew E 14 = Z_to_bv 64 (c_h cx)) by (rewrite (HE 14%nat 14%bv eq_refl); exact G14).
assert (HE33 : ew E 33 = Z_to_bv 64 (c_img cx)) by (apply (HX 1%nat); reflexivity).
pose proof (bv_unsigned_in_range 64 (getr regs0 3)) as Rgp. change (bv_modulus 64) with (2 ^ 64) in Rgp.
assert (HS : st_ok ubs0segs E ssC0 (mkst regs1 (Z_to_bv 64 PC_C) mem1 (seg_rom ubs0segs))).
{ subst E. unfold ssC0.
apply (ra_st_okW cx (c_rcur cx) regs1 [] mem1 PC_C _ 0 0 false [] _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact G10].
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE18, HE25, HE13, HE14, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_C) mem1 (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_LZW_GenerateStream; [eapply ra_wr_okW; [exact HE2 | lia | lia | intros X; lia | left; cbn; lia]|].
jreg HS (10%bv:reg) as A10. cbn [sv_denot] in A10. rewrite HE2 in A10.
pose proof (st_ok_reg _ _ _ _ (11%bv:reg) HS) as A11. eval_sr_get_in A11. rewrite denot_lit_U in A11.
rewrite (U_mulw_small _ _ _ (c_h cx) (c_w cx) (U_atom _ 14 _ HE14 ltac:(lia)) (U_atom _ 13 _ HE13 ltac:(lia))) in A11 by lia.
replace (c_h cx * c_w cx) with (c_nP cx) in A11 by (unfold c_nP; lia).
jreg HS (12%bv:reg) as A12. rewrite HE33 in A12.
jreg HS (13%bv:reg) as A13. rewrite HE25 in A13.
jreg HS (14%bv:reg) as A14. rewrite HE18 in A14.
jreg HS (1%bv:reg) as Ara. jreg HS (2%bv:reg) as Asp. rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2 in Asp.
jreg HS (4%bv:reg) as A4. rewrite (HE 4%nat 4%bv eq_refl), R4, Htpv in A4.
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [3; 8; 9; 22; 23; 24; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
assert (MEQ : forall a, ~ (c_sp cx - 16 <= a < c_sp cx + 48) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs mem1 a).
{ intros a Hna Ha. mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (Hobjs' : objs_at (ms_mem ms) cx (c_rcur cx)).
{ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; apply MEQ; lia. }
assert (HFBC' : fbC (ms_mem ms) cx).
{ eapply fbC_kept; [exact HFBC | |]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H). }
assert (HFS' : frame_savedN ubs0_msyms 12 regs0 (ms_mem ms) (spZ regs0)).
{ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]. intros a Ha. apply MEQ; lia. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
assert (Hsp_l : spZ (ms_regs ms) = c_sp cx) by (unfold spZ; rewrite Asp; apply unsigned_lit_small; lia).
assert (HIMGc : garr8 ubs0segs (ms_mem ms) (c_img cx) IMGV).
{ apply (garr8_frame ubs0segs mem (ms_mem ms) (c_img cx) IMGV HIMG0). rewrite HIMGlen. pose proof HJ as (_ & _ & _ & Hkeep & _).
intros a Ha. unfold c_nP in Ha. replace a with (c_img cx + (a - c_img cx)) by lia. apply (Hkeep (c_img cx) (c_Nimg cx) (a - c_img cx) Himgin Himgin1); [lia|].
intros (r & [<- | []] & Hr); cbn [fst snd] in Hr; lia. }
eapply SR_bind.
{ unfold lzw_specX in LZW.
eapply (LZW RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 (ms_mem ms) md1 (ms_regs ms)
(c_sp cx + 8) (c_nP cx) (c_img cx) idl icl (c_img cx) (c_Nimg cx) IMGV b);
rewrite ?Hsp_l; try first [exact HJ | exact Hid | exact A10 | exact A11 | exact A12 | exact A13 | exact A14 | exact A4 | exact Himgin1 | exact HIMGc | exact HRq].
- rewrite Ara. apply ret_ok_even. vm_compute. reflexivity.
- exact Hspal.
- lia.
- lia.
- lia.
- replace (c_sp cx + 8) with (c_sp cx + 1 * 8) by lia. rewrite Z.mod_add by lia.
rewrite (Znumtheory.Zmod_div_mod 8 16 (c_sp cx)); [rewrite Hspal; reflexivity | lia | lia | exists 2; reflexivity].
- unfold c_nP. lia.
- lia.
- lia.
- lia.
- unfold c_nP. lia.
- eapply rodata_ok_of_heap. exact (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
- rewrite <- HIMGlen, Nat2Z.id. reflexivity.
-   apply rawadd_room_lzw0; [unfold c_nP; lia | exact HRM]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJ2 & Hid2 & HP2 & Hres10 & MHI & MBL & Hcase).
rewrite Hsp_l in MHI. rewrite Ara.
jafter_call_keep HS 69%nat regs2 mem2 HP2 [1%nat; 2%nat; 3%nat] HS2.
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
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (RA0 + 0x210)) mem2 (seg_rom ubs0segs))) in HJ2.
destruct Hcase as [(-> & bb & Lbb & M & HB2 & Hw & W1 & W2 & HM & HM2 & HVOK & HRo) | (Hres & HB2 & HpR & HVNONE & HRo)].
-
pin_reg' HS (10%bv:reg) 0 Hres10.
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_OK.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret. right.
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [2; 3; 4; 8; 9; 22; 23; 24; 27]%bv HS ltac:(apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]) ltac:(vm_compute; reflexivity)) as HK3.
cbn [ms_regs mkst] in HK3.
assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs mem2 a).
{ intros a Ha. apply mbyte_eq_of1'. lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _) end. }
exists L2, A2, (ms_regs ms0), (ms_mem ms0), md2, bb, Lbb, M.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [apply ra_rb_plain; [lia | exact HRo]|].
split. { unfold ra_regs. rewrite !HK3 by (cbv; tauto). exact HR. }
split; [rewrite HK3 by (cbv; tauto); exact G23|].
split; [rewrite HK3 by (cbv; tauto); exact G24|].
split; [rewrite HK3 by (cbv; tauto); exact G22|].
split. { eapply Permutation_trans; [exact HB2|]. apply perm_skip. exact HB1. }
split; [exact Hw|].
split. { intros k Hk. rewrite MEQ3 by lia. apply W1. exact Hk. }
split. { intros k Hk. rewrite MEQ3 by lia. replace (c_sp cx + 16) with (c_sp cx + 8 + 8) by lia. apply W2. exact Hk. }
split; [exact HM|].
split. { eapply objs_at_kept; [exact Hobjs2 | | |]; intros i Hi; apply MEQ3; lia. }
split. { eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS2|]. intros a Ha. apply MEQ3; lia. }
destruct (heap_blocks_range _ _ LAWS L2 A2 _ _ bb Lbb (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) ltac:(eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]) ltac:(lia)) as (Hbb0 & Hbb1 & _).
replace (ra_iclen cx) with icl by exact Hiclv. rewrite <- Hidlv. replace (ra_pix cx IMGV) with IMGV by (unfold ra_pix, YO07.flag; rewrite Hl0; reflexivity).
split; [| split; [exact HM2|]].
{ destruct HVOK as (out & Hout & HGout & HMout). exists out. split; [exact Hout|]. split; [| exact HMout].
apply (garr8_frame ubs0segs mem2 (ms_mem ms0) bb out HGout). intros a Ha. apply MEQ3. lia. }
eapply fbC_kept; [exact HFBC' | |]; intros a Ha; rewrite MEQ3 by lia; apply MHI; lia.
-
jreg HS (10%bv:reg) as P10. cbn [ms_regs mkst] in P10. rewrite Hres10 in P10. symmetry in P10.
add_fact' HS 73%nat (mkAF 2 5 0). 2:{ rewrite P10, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
jrun_to LAWS ubs0tbl_ok HS HJ2 PC_ST.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ [2; 3; 4; 8; 27]%bv HS ltac:(apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]) ltac:(vm_compute; reflexivity)) as HK3.
cbn [ms_regs mkst] in HK3.
jreg HS (18%bv:reg) as Q18. cbn [ms_regs mkst] in Q18.
assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs mem2 a).
{ intros a Ha. apply mbyte_eq_of1'. lazymatch goal with HF : frame_of _ _ _ _ |- _ => exact (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) _) end. }
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono; [| cbv beta; intros c' Hc'; left; exact Hc'].
eapply (ra_st_R API IMG [(c_raw cx + 40, c_raw cx + 44)] (ra_exitX cx IMGV LCTV) (fun s => res_ok s (rawadd_rb b)) cx L A mem md L2 A2 md2 regs0 (ms_regs ms0) (ms_mem ms0) (c_rcur cx));
[ exact (proj1 Hcx) | exact HO | exact HJ2 | exact Hid2 | apply ra_rb_plain_eidx; exact HRo | | exact Hrawin | | | | | | | | exact Q18
| intros a Ha; exists (c_raw cx + 40, c_raw cx + 44); split; [left; reflexivity | cbn; lia]
| rewrite P10, unsigned_lit_small by lia; rewrite Hres;
exists 5; rewrite (ra_model_lzw cx IMGV LCTV Hrc (proj2 Hcx));
replace (ra_iclen cx) with icl by exact Hiclv; rewrite <- Hidlv; replace (ra_pix cx IMGV) with IMGV by (unfold ra_pix, YO07.flag; rewrite Hl0; reflexivity);
unfold lzw_vnone in HVNONE; rewrite HVNONE; split; [reflexivity | split; reflexivity] ]; cbn [ms_regs ms_mem].
+ eapply Permutation_trans; [exact HB2 | exact HB1].
+ eapply obj_at_transport_range; [exact (proj1 (proj2 Hobjs2)) | exact (proj1 LAY_Raw_ok) |]. intros i Hi. apply MEQ3. lia.
+ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS2|]. intros a Ha. apply MEQ3; lia.
+ rewrite HK3 by (cbv; tauto). exact R2.
+ rewrite HK3 by (cbv; tauto). rewrite R3, Hgp0. reflexivity.
+ rewrite HK3 by (cbv; tauto). rewrite R4, Htp0. reflexivity.
+ rewrite HK3 by (cbv; tauto). rewrite R27, H27o. reflexivity.
+ rewrite HK3 by (cbv; tauto). exact R8.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
