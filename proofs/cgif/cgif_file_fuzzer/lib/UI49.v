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
YI06 UI5b YI09 YI08 YI0r YI0o YI6a UI1w UI3p UI3m UI3t
UI4l UI3w UI4j UI4i UI4k UI4g UI43.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w UI2v UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Variables (IMGV LCTV : list Z).
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Lemma ra_t2_lctp6 :
forall cx L A mem md L2 A2 md2 (regs0 regs2 : bvmap 5 word) (mem2 : word -> option byte) (p bb Lbb M : Z) (S : list Z) (b : rbound),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs0_msyms MR RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) L A mem md L2 A2 mem2 md2 ->
st_init_done A2 = true -> ra_rb b A2 Lbb -> Permutation (blocks L A) (c_blocks cx) ->
ra_regs regs2 cx -> getr regs2 23 = Z_to_bv 64 (c_slct cx) -> getr regs2 24 = Z_to_bv 64 p -> getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) ->
c_slct cx <> 0 -> c_slct cx <= 2 ^ p -> p = 6 ->
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) ->
wtok' RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) (blocks L A) (bb, Lbb) ->
word_mem ubs0segs mem2 (c_sp cx + 8) bb -> val_mem ubs0segs mem2 (c_sp cx + 16) 4 M -> 1 <= M <= Lbb ->
objs_at mem2 cx (c_rcur cx) -> frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) ->
getr regs2 19 = Z_to_bv 64 0 ->
p = YO07.pal_pow (c_slct cx) ->
(exists Nl, In (c_lct cx, Nl) (c_rest cx) /\ 3 * c_slct cx <= Nl /\ (c_lct cx, Nl) <> (c_f cx, FILE_BLOCK) /\
garr8 ubs0segs mem (c_lct cx) LCTV /\ 3 * c_slct cx <= Z.of_nat (length LCTV)) ->
lzw_vok (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) mem2 bb M -> M <= 2 * c_nP cx + 16 -> fbC mem2 cx ->
sink_at ubs0_msyms mem2 md2 (c_f cx) (S ++ ra_gce cx) -> Z.of_nat (length S) + 2 * c_nP cx + 2048 <= SINK_MAX ->
SR ubs0segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs0segs)) md2)
(at_T3 API IMGV LCTV cx L A mem md regs0 S b).
Proof using FWRITE IMG.
intros cx L A mem md L2 A2 md2 regs0 regs2 mem2 p bb Lbb M S b Hcx HO HJ Hid HRB HB HR G23 G24 G22 Hnz Hsk Hp HB2 Hwt W32 W40 HM Hobjs HFS G19 Hpp HLCT HVOK HM2 HFBC HSK Hroom.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
assert (Hbbin : In (bb, Lbb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 bb Lbb HH2 Hbbin ltac:(lia)) as (Hbb0 & Hbb1 & _).
set (M' := M mod 2 ^ 32).
pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)) as HM'. fold M' in HM'.
assert (W40' : val_mem ubs0segs mem2 (c_sp cx + 16) 4 M') by (subst M'; change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)); apply (proj1 (val_mem_mod _ _ _ _)); exact W40).
remember (Ereg regs2 (ra_extra cx (c_rcur cx) [bb; M'])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs2 cx (c_rcur cx) [bb; M']) as HX. pose proof (E_rv regs2 cx (c_rcur cx) [bb; M']) as HY. rewrite <- HE0 in HX, HY.
pose proof (E_morev regs2 cx (c_rcur cx) [bb; M'] LG) as HMo. rewrite <- HE0 in HMo.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE23 : ew E 23 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE40 : ew E 40 = Z_to_bv 64 (c_slct cx)) by (apply (HX 8%nat); reflexivity).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE69 : ew E 69 = Z_to_bv 64 bb) by (apply (HMo 0%nat); reflexivity).
assert (HE70 : ew E 70 = Z_to_bv 64 M') by (apply (HMo 1%nat); reflexivity).
assert (CASE : forall pl K : Z, p = pl -> K = 2 ^ pl -> 1 <= c_slct cx <= K -> K <= 256 ->
(forall E0, st_ok ubs0segs E0 (ssT2l pl K) (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs0segs)) -> E0 = E ->
SR ubs0segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs0segs)) md2) (at_T3 API IMGV LCTV cx L A mem md regs0 S b)) ->
SR ubs0segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs0segs)) md2) (at_T3 API IMGV LCTV cx L A mem md regs0 S b)).
{ intros pl K Hpl HK Hsk2 HK2 RUN. apply (RUN E); [|reflexivity]. subst E. unfold ssT2l.
apply (ra_st_okW cx (c_rcur cx) regs2 [bb; M'] mem2 PC_T2 _ 47 48 false _ _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite G24, Hpl; reflexivity]
| intros X; discriminate X | cbn [sv_denot]; rewrite G22, HE9, unsigned_lit_small by lia; reflexivity] | intros X; discriminate X | cbn [sv_denot]; exact G19].
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W32].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact W40'].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE23, HE40, HE70, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor.
}
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs0segs))) in HJ.
rewrite Hp in Hsk; cbn in Hsk.
apply (CASE 6 64); [lia | reflexivity | lia | lia |]. intros E0 HS HEE; rewrite HEE in HS; clear HEE E0.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_writecb; [wrW HE2|].
assert (HWv : WRITECB_STK = 528) by reflexivity. assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
assert (HE35 : ew E 35 = Z_to_bv 64 (c_w cx)) by (apply (HX 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 (c_h cx)) by (apply (HX 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 (c_top cx)) by (apply (HX 5%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 (c_left cx)) by (apply (HX 6%nat); reflexivity).
assert (HE32 : ew E 32 = Z_to_bv 64 (c_lct cx)) by (apply (HX 0%nat); reflexivity).
assert (Rpk : 0 <= ra_packed cx < 256).
{ unfold ra_packed. rewrite <- Hpp. replace (c_slct cx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). cbn [negb]. destruct (YO07.flag (c_fattr cx) 2); lia. }
assert (Lgce : (length (ra_gce cx) <= 8)%nat) by (unfold ra_gce; destruct (_ || _); cbn; lia).
jreg HS (10%bv:reg) as Wa10. jreg HS (11%bv:reg) as Wa11. jreg HS (12%bv:reg) as Wa12. jreg HS (2%bv:reg) as Wa2. jreg HS (4%bv:reg) as Wa4. jreg HS (1%bv:reg) as Wa1.
rewrite HE44 in Wa10. rewrite HE2 in Wa11.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Wsp : spZ (ms_regs msx) = c_sp cx) by (unfold spZ; rewrite Wa2, <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2; apply unsigned_lit_small; lia) end.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2c.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (MEQ1 : forall a, ~ (c_sp cx + 47 <= a < c_sp cx + 48) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem2 a)
by (intros a Hna Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H));
assert (Hobjs1 : objs_at (ms_mem msx) cx (c_rcur cx)) by (eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; apply MEQ1; lia);
assert (HFBC1 : fbC (ms_mem msx) cx) by (eapply fbC_kept; [exact HFBC | |]; intros a Ha; apply MEQ1; lia);
assert (HSKc : sink_at ubs0_msyms (ms_mem msx) md2 (c_f cx) (S ++ ra_gce cx))
by (apply (sink_at_frame ubs0_msyms mem2 _ md2 (c_f cx)); [| exact HSK]; intros a Ha;
assert (Ha' : 0 <= a < alloc_ceiling) by (clear - Ha Hf0 Hf1 Hac; destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]);
apply MEQ1; clear - Ha' Hsplo Hac; lia);
pose proof (fbC_hdr _ cx (c_rcur cx) (objs_fields_ok _ _ _ Hobjs) Rpk HFBC1) as HGB
end.
assert (Hgin : In (c_g cx, CGIF_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; left; reflexivity]).
assert (HfinA : In (c_f cx, FILE_BLOCK) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; right; right; exact Hfin]).
assert (Hgin2 : In (c_g cx, CGIF_SIZE) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact Hgin]).
assert (Hfin2 : In (c_f cx, FILE_BLOCK) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact HfinA]).
assert (Hrawin : In (c_raw cx, RAW_SIZE) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hrawin2 : In (c_raw cx, RAW_SIZE) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact Hrawin]).
assert (Hrf : c_raw cx + 48 <= c_f cx \/ c_f cx + FILE_BLOCK <= c_raw cx).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L2 A2 _ md2 (c_raw cx, RAW_SIZE) (c_f cx, FILE_BLOCK) HH2c Hrawin2 Hfin2 ltac:(intros X; injection X; lia)) as Hd. cbn [fst snd] in Hd. lia. }
assert (Hgf : c_g cx + 96 <= c_f cx \/ c_f cx + FILE_BLOCK <= c_g cx).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L2 A2 _ md2 (c_g cx, CGIF_SIZE) (c_f cx, FILE_BLOCK) HH2c Hgin2 Hfin2 ltac:(intros X; injection X; lia)) as Hd. cbn [fst snd] in Hd. lia. }
assert (Hbf : bb + Lbb <= c_f cx \/ c_f cx + FILE_BLOCK <= bb).
{ pose proof (heap_sep_perm ubs0_msyms MR LAWS L2 A2 _ md2 (bb, Lbb) _ (c_f cx, FILE_BLOCK) HH2c HB2 HfinA) as Hd. cbn [fst snd] in Hd. exact Hd. }
eapply SR_bind.
{ eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := c_g cx) (gvals := c_gvals cx) (src := c_sp cx + 37) (n := 10) (f := c_f cx) (S := S ++ ra_gce cx) (bs := ra_hdr cx);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Wa1 | apply ret_ok_even; vm_compute; reflexivity
| exact Wa10 | exact Wa11 | exact Wa12 | rewrite Wsp; exact Hspal | rewrite Wsp; lia | rewrite Wsp; lia | rewrite Wsp; lia
| rewrite Wa4, (HE 4%nat 4%bv eq_refl), R4, Htpv; reflexivity
| exact (proj2 (proj2 Hobjs1)) | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSKc | exact HGB | reflexivity
| lia | lia | lia | rewrite Wsp; lia | rewrite length_app; unfold c_nP in Hroom; lia | lia | ].
intros a Ha. destruct Ha as (r & Hr & Har). exists r. split; [right; exact Hr | exact Har]. }
cbv beta. intros c' (regsW & memW & mdW & -> & HJW & HPW & Hr10W & HSKW & HhiW & HblkW). rewrite Wsp in HhiW.
jafter_call2 HS 71%nat regsW memW HPW 0 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HE2 | exact HhiW | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 9); [rewrite HE9; apply unsigned_lit_small; lia | exact HhiW | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise ubs0segs _ _ _ 8); [rewrite HE8; apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. replace a with (c_raw cx + (a - c_raw cx)) by lia. apply (HblkW (c_raw cx) RAW_SIZE (a - c_raw cx) Hrawin2); [clear - Ha HRSv; lia|].
replace (c_raw cx + (a - c_raw cx)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; clear - Ha Hr Hraw0 Hrf HFBv HRSv; lia.
- eapply (region_kept_pointwise ubs0segs _ _ _ 44); [rewrite HE44; apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. replace a with (c_g cx + (a - c_g cx)) by lia. apply (HblkW (c_g cx) CGIF_SIZE (a - c_g cx) Hgin2); [clear - Ha HGSv; lia|].
replace (c_g cx + (a - c_g cx)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; clear - Ha Hr Hg0 Hgf HFBv HGSv; lia. }
clear HS. rename HS2 into HS.
pin_regR HS (10%bv:reg) 0 Hr10W.
lazymatch type of HS with st_ok _ _ _ ?msx => change memW with (ms_mem msx) in HJW end.
assert (KW_stk : forall a, c_sp cx <= a < c_sp cx + 144 -> ~ (c_sp cx + 47 <= a < c_sp cx + 48) -> mbyte ubs0segs memW a = mbyte ubs0segs mem2 a)
by (clear - HhiW MEQ1 Hsplo Hac Hsp47 HWv; intros a H1 H2; etransitivity; [apply (proj1 (HhiW a ltac:(lia) ltac:(lia)))|]; apply MEQ1; lia).
assert (KW_cfg : forall i, 0 <= i < 40 -> mbyte ubs0segs memW (c_cfp cx + i) = mbyte ubs0segs mem2 (c_cfp cx + i))
by (clear - HhiW MEQ1 Hsplo Hac Hsp47 HWv Hcfplo Hcfphi; intros i Hi; etransitivity; [apply (proj1 (HhiW (c_cfp cx + i) ltac:(lia) ltac:(lia)))|]; apply MEQ1; lia).
assert (KW_blk : forall b n i, In (b, n) (blocks L2 A2) -> b + n <= alloc_ceiling -> 4096 <= b -> (b + n <= c_f cx \/ c_f cx + FILE_BLOCK <= b) -> 0 <= i < n ->
mbyte ubs0segs memW (b + i) = mbyte ubs0segs mem2 (b + i))
by (clear - HblkW MEQ1 Hsplo Hac HFBv; intros b n i Hin Hhi Hlo Hsep Hi; etransitivity; [apply (HblkW b n i Hin Hi); intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia|];
apply MEQ1; lia).
jrun_to LAWS ubs0tbl_ok HS HJW ubs0_A_cgif_writecb.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
destruct HLCT as (Nl & HlctR & H3Nl & Hlctne & HGL & HLlen).
assert (HlctA : In (c_lct cx, Nl) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; right; right; exact HlctR]).
assert (Hlct2 : In (c_lct cx, Nl) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | right; exact HlctA]).
pose proof (heap_blocks_range ubs0_msyms MR LAWS L2 A2 _ _ (c_lct cx) Nl HH2c Hlct2 ltac:(lia)) as (Rl0 & Rl1 & _).
assert (HB2r : Permutation (blocks L2 A2) ((c_raw cx, RAW_SIZE) :: (bb, Lbb) :: (c_g cx, CGIF_SIZE) :: (c_img cx, c_Nimg cx) :: c_rest cx)).
{ eapply Permutation_trans; [exact HB2|]. eapply Permutation_trans; [apply perm_skip; exact HB|]. apply perm_swap. }
assert (Hrl : c_raw cx + RAW_SIZE <= c_lct cx \/ c_lct cx + Nl <= c_raw cx).
{ pose proof (heap_sep_perm ubs0_msyms MR LAWS L2 A2 _ md2 (c_raw cx, RAW_SIZE) _ (c_lct cx, Nl) HH2c HB2r ltac:(right; right; right; exact HlctR)) as Hd. cbn [fst snd] in Hd. exact Hd. }
assert (Hfl : c_lct cx + Nl <= c_f cx \/ c_f cx + FILE_BLOCK <= c_lct cx).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L2 A2 _ md2 (c_lct cx, Nl) (c_f cx, FILE_BLOCK) HH2c Hlct2 Hfin2 Hlctne) as Hd. cbn [fst snd] in Hd. exact Hd. }
jreg HS (10%bv:reg) as Xa10. jreg HS (11%bv:reg) as Xa11. jreg HS (2%bv:reg) as Xa2. jreg HS (4%bv:reg) as Xa4. jreg HS (1%bv:reg) as Xa1.
pose proof (st_ok_reg _ _ _ _ (12%bv:reg) HS) as Xa12. eval_sr_get_in Xa12. cbn [sv_denot] in Xa12.
rewrite HE44 in Xa10. rewrite HE32 in Xa11. rewrite ew_havoc_old in Xa12 by (cbv; lia). rewrite HE40, unsigned_lit_small, Z.add_0_r in Xa12 by lia.
assert (Hmul : mul_div M_MUL (Z_to_bv 64 (c_slct cx)) (Z_to_bv 64 3) = Z_to_bv 64 (3 * c_slct cx)).
{ apply bv_eq. rewrite mul_div_unsigned. cbn [zmd_raw]. rewrite !unsigned_lit_small by lia. rewrite bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia). lia. }
rewrite Hmul in Xa12.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Xsp : spZ (ms_regs msx) = c_sp cx) by (unfold spZ; rewrite Xa2, <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2; apply unsigned_lit_small; lia) end.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (MEQ2 : forall a, ~ (c_sp cx + 47 <= a < c_sp cx + 48) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs memW a)
by (intros a Hna Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H));
assert (Hobjs2 : objs_at (ms_mem msx) cx (c_rcur cx))
by (eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; rewrite MEQ2 by (clear - Hi Hcfplo Hcfphi Hsplo Hac Hraw0 Hraw1 Hg0 Hg1 HRSv HGSv; lia); [apply KW_cfg; exact Hi | apply (KW_blk _ _ i Hrawin2); clear - Hi Hraw0 Hraw1 Hrf HRSv HFBv; lia | apply (KW_blk _ _ i Hgin2); clear - Hi Hg0 Hg1 Hgf HGSv HFBv; lia]);
assert (HSK2 : sink_at ubs0_msyms (ms_mem msx) mdW (c_f cx) ((S ++ ra_gce cx) ++ ra_hdr cx))
by (apply (sink_at_frame ubs0_msyms memW _ mdW (c_f cx)); [| exact HSKW]; intros a Ha;
assert (Ha' : 0 <= a < alloc_ceiling) by (clear - Ha Hf0 Hf1 Hac; destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]);
apply MEQ2; clear - Ha' Hsplo Hac; lia);
assert (HG3 : garr8 ubs0segs (ms_mem msx) (c_lct cx) (firstn (Z.to_nat (3 * c_slct cx)) LCTV))
end.
{ pose proof (garr8_sub ubs0segs mem (c_lct cx) LCTV 0%nat (Z.to_nat (3 * c_slct cx)) HGL) as HGs. cbn [skipn Z.of_nat] in HGs. rewrite Z.add_0_r in HGs.
apply (garr8_frame ubs0segs mem _ (c_lct cx) _ HGs).
assert (HLn : (Z.to_nat (3 * c_slct cx) <= length LCTV)%nat) by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; exact HLlen).
rewrite firstn_length_le by exact HLn. rewrite Z2Nat.id by lia.
pose proof HJW as (_ & _ & _ & Hkeep & _). intros a Ha.
replace a with (c_lct cx + (a - c_lct cx)) by lia. apply (Hkeep (c_lct cx) Nl (a - c_lct cx) HlctA Hlct2); [clear - Ha H3Nl Hnz F8; lia|].
intros (r & [<- | [<- | [<- | []]]] & Hr); cbn [fst snd sink_token] in Hr; clear - Ha Hr Hrl Hfl Rl0 Rl1 H3Nl HFBv HRSv F8 Hnz; lia. }
assert (HLn : (Z.to_nat (3 * c_slct cx) <= length LCTV)%nat) by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; exact HLlen).
assert (HL3 : Z.of_nat (length (firstn (Z.to_nat (3 * c_slct cx)) LCTV)) = 3 * c_slct cx) by (rewrite firstn_length_le by exact HLn; lia).
assert (Lhdr : length (ra_hdr cx) = 10%nat) by reflexivity.
eapply SR_bind.
{ eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := c_g cx) (gvals := c_gvals cx) (src := c_lct cx) (n := 3 * c_slct cx) (f := c_f cx) (S := (S ++ ra_gce cx) ++ ra_hdr cx) (bs := firstn (Z.to_nat (3 * c_slct cx)) LCTV);
[ exact HS | reflexivity | reflexivity | exact HJW | exact Xa1 | apply ret_ok_even; vm_compute; reflexivity
| exact Xa10 | exact Xa11 | exact Xa12 | rewrite Xsp; exact Hspal
| rewrite Xsp; clear - Hspe HSTKv Hsplo Hac HWv; lia | rewrite Xsp; clear - Hspe; lia | rewrite Xsp; clear - Hsp47; lia
| rewrite Xa4, (HE 4%nat 4%bv eq_refl), R4, Htpv; reflexivity
| exact (proj2 (proj2 Hobjs2)) | exact Hwfn | exact Hfile | exact Hgin2 | exact Hfin2 | exact HSK2 | exact HG3 | rewrite HL3; reflexivity
| clear - Rl0; lia | clear - Rl1 H3Nl Hac Hnz; lia | clear - Hfl H3Nl Hnz; lia | rewrite Xsp; clear - Rl1 H3Nl Hac Hsplo Hnz HWv; lia
| rewrite !length_app, Lhdr; unfold c_nP in Hroom; clear - Hroom Lgce Hsk Hnz Hw1 Hh1; lia | clear - Hsk Hnz; lia | ].
intros a Ha. destruct Ha as (r & Hr & Har). exists r. split; [right; exact Hr | exact Har]. }
cbv beta. intros c' (regsX & memX & mdX & -> & HJX & HPX & Hr10X & HSKX & HhiX & HblkX). rewrite Xsp in HhiX.
lazymatch type of HS with st_ok _ ?Ec _ _ => lazymatch Ec with havoc _ ?k0 ?l0 => let k := eval vm_compute in (k0 + length l0)%nat in
jafter_call2 HS k regsX memX HPX 0 [0%nat; 1%nat; 2%nat] HS2 end end.
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havoc; exact HE2 | exact HhiX | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 9); [ew_havoc; rewrite HE9; apply unsigned_lit_small; lia | exact HhiX | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_pointwise ubs0segs _ _ _ 8); [ew_havoc; rewrite HE8; apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. replace a with (c_raw cx + (a - c_raw cx)) by lia. apply (HblkX (c_raw cx) RAW_SIZE (a - c_raw cx) Hrawin2); [clear - Ha HRSv; lia|].
replace (c_raw cx + (a - c_raw cx)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; clear - Ha Hr Hraw0 Hrf HFBv HRSv; lia.
- eapply (region_kept_pointwise ubs0segs _ _ _ 44); [ew_havoc; rewrite HE44; apply unsigned_lit_small; lia | | cbn; lia].
cbn [r_lo r_hi]. intros a Ha. replace a with (c_g cx + (a - c_g cx)) by lia. apply (HblkX (c_g cx) CGIF_SIZE (a - c_g cx) Hgin2); [clear - Ha HGSv; lia|].
replace (c_g cx + (a - c_g cx)) with a by lia. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; clear - Ha Hr Hg0 Hgf HFBv HGSv; lia. }
clear HS. rename HS2 into HS.
pin_regR HS (10%bv:reg) 0 Hr10X.
lazymatch type of HS with st_ok _ _ _ ?msx => change memX with (ms_mem msx) in HJX end.
assert (KX_stk : forall a, c_sp cx <= a < c_sp cx + 144 -> ~ (c_sp cx + 47 <= a < c_sp cx + 48) -> mbyte ubs0segs memX a = mbyte ubs0segs mem2 a)
by (clear - HhiX MEQ2 KW_stk Hsplo Hac Hsp47 HWv; intros a H1 H2; etransitivity; [apply (proj1 (HhiX a ltac:(lia) ltac:(lia)))|]; rewrite MEQ2 by lia; apply KW_stk; lia).
assert (KX_cfg : forall i, 0 <= i < 40 -> mbyte ubs0segs memX (c_cfp cx + i) = mbyte ubs0segs mem2 (c_cfp cx + i))
by (clear - HhiX MEQ2 KW_cfg Hsplo Hac Hsp47 HWv Hcfplo Hcfphi; intros i Hi; etransitivity; [apply (proj1 (HhiX (c_cfp cx + i) ltac:(lia) ltac:(lia)))|]; rewrite MEQ2 by lia; apply KW_cfg; lia).
assert (KX_blk : forall b n i, In (b, n) (blocks L2 A2) -> b + n <= alloc_ceiling -> 4096 <= b -> (b + n <= c_f cx \/ c_f cx + FILE_BLOCK <= b) -> 0 <= i < n ->
mbyte ubs0segs memX (b + i) = mbyte ubs0segs mem2 (b + i))
by (clear - HblkX MEQ2 KW_blk Hsplo Hac HFBv; intros b n i Hin Hhi Hlo Hsep Hi; etransitivity; [apply (HblkX b n i Hin Hi); intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia|];
rewrite MEQ2 by lia; apply (KW_blk b n i Hin Hhi Hlo Hsep Hi)).
jrun_to LAWS ubs0tbl_ok HS HJX PC_WDB.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jbranch ubs0tbl HS.
{ exfalso. rewrite branch_ne_U, (t2_chk_ne _ 40 (c_slct cx) 64) in Hc by (first [ew_havoc; exact HE40 | lia]). discriminate Hc. }
clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJX PC_WDB.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jbranch ubs0tbl HS.
+
rewrite branch_eq_U, (t2_cnt_U _ 40 (c_slct cx) 64), U_lit in Hc by (first [ew_havoc; exact HE40 | reflexivity | lia]).
assert (HsK : c_slct cx = 64) by (destruct (Z.eqb_spec (3 * (64 - c_slct cx)) 0); [lia | discriminate]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJX PC_T3.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 27]%bv HS ltac:(apply env_agree_havoc_ge; [cbv; lia | apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]]) ltac:(vm_compute; reflexivity)) as HKF.
lazymatch type of HS with st_ok _ _ _ ?msx =>
cbn [ms_regs mkst] in HKF;
assert (MEQ3 : forall a, ~ (c_sp cx + 47 <= a < c_sp cx + 48) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs memX a)
by (intros a Hna Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H));
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HRF;
assert (KF_stk : forall a, c_sp cx <= a < c_sp cx + 144 -> ~ (c_sp cx + 47 <= a < c_sp cx + 48) -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem2 a)
by (clear - MEQ3 KX_stk Hsplo Hac Hsp47; intros a H1 H2; rewrite MEQ3 by lia; apply KX_stk; lia);
assert (KF_cfg : forall i, 0 <= i < 40 -> mbyte ubs0segs (ms_mem msx) (c_cfp cx + i) = mbyte ubs0segs mem2 (c_cfp cx + i))
by (clear - MEQ3 KX_cfg Hsplo Hac Hsp47 Hcfplo Hcfphi; intros i Hi; rewrite MEQ3 by lia; apply KX_cfg; lia);
assert (KF_blk : forall b n i, In (b, n) (blocks L2 A2) -> b + n <= alloc_ceiling -> 4096 <= b -> (b + n <= c_f cx \/ c_f cx + FILE_BLOCK <= b) -> 0 <= i < n ->
mbyte ubs0segs (ms_mem msx) (b + i) = mbyte ubs0segs mem2 (b + i))
by (clear - MEQ3 KX_blk Hsplo Hac; intros b n i Hin Hhi Hlo Hsep Hi; rewrite MEQ3 by lia; apply (KX_blk b n i Hin Hhi Hlo Hsep Hi))
end.
jreg HS (18%bv:reg) as Q18. rewrite ?ew_havoc_old in Q18 by (cbv; lia). rewrite HE44 in Q18.
jreg HS (20%bv:reg) as Q20. jreg HS (19%bv:reg) as Q19.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- at_T3 _ _ _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) =>
exists L2, A2, (ms_regs msx), (ms_mem msx), mdX, bb, Lbb, M end.
split; [reflexivity|]. split; [exact HJX|]. split; [exact Hid|]. split; [exact HRB|].
cbn [ms_regs ms_mem mkst] in *.
split; [rewrite HKF by (cbv; tauto); exact R2|]. split; [rewrite HKF by (cbv; tauto); exact R8|].
split; [rewrite HKF by (cbv; tauto); rewrite R4, Htpv; reflexivity|]. split; [rewrite HKF by (cbv; tauto); exact R3|].
split; [rewrite HKF by (cbv; tauto); exact R27|].
split; [exact Q18|]. split; [exact Q20|].
split; [exact HB2|]. split; [exact Hwt|].
split. { apply val_mem_word_mem. eapply (fb_of_region _ _ _ _ _ _ _ _ 8 8%N (SOff 69%nat 0) bb HRF); [ew_havoc; exact HE2 | cbv; tauto | cbn [sv_denot]; ew_havoc; rewrite HE69, unsigned_lit_small, Z.add_0_r by (clear - Hbb0 Hbb1 Hac HM; lia); reflexivity | cbn; clear - Hbb0 Hbb1 Hac HM; lia | cbn; lia]. }
split. { change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)) in W40'. apply (proj2 (val_mem_mod _ _ _ _)). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). fold M'.
eapply (fb_of_region _ _ _ _ _ _ _ _ 16 4%N (SOff 70%nat 0) M' HRF); [ew_havoc; exact HE2 | cbv; tauto | cbn [sv_denot]; ew_havoc; rewrite HE70, unsigned_lit_small, Z.add_0_r by (clear - HM'; lia); reflexivity | cbn; clear - HM'; lia | cbn; lia]. }
split; [exact HM|].
split. { eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; [apply KF_cfg; exact Hi | apply (KF_blk _ _ i Hrawin2); clear - Hi Hraw0 Hraw1 Hrf HRSv HFBv; lia | apply (KF_blk _ _ i Hgin2); clear - Hi Hg0 Hg1 Hgf HGSv HFBv; lia]. }
split. { eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]. intros a Ha. apply KF_stk; clear - Ha Hspe; lia. }
split. { destruct HVOK as (out & Hout & HGout & HMout). exists out. split; [exact Hout|]. split; [|exact HMout].
apply (garr8_frame ubs0segs mem2 _ bb out HGout). intros a Ha. rewrite <- HMout in Ha. replace a with (bb + (a - bb)) by lia. apply (KF_blk _ _ (a - bb) Hbbin); clear - Ha Hbb0 Hbb1 Hbf HM; lia. }
split; [exact HM2|].
split. { eapply fb_kept1; [exact (proj1 HFBC) | intros a Ha; cbn in Ha; apply KF_stk; clear - Ha Hspe; lia]. }
replace (ra_lctb cx LCTV) with (firstn (Z.to_nat (3 * c_slct cx)) LCTV).
2:{ unfold ra_lctb. replace (c_slct cx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). cbn [negb]. rewrite <- Hpp, Hp, HsK. cbn. rewrite app_nil_r. reflexivity. }
split. { rewrite <- !app_assoc in HSKX.
apply (sink_at_frame ubs0_msyms memX _ mdX (c_f cx)); [| exact HSKX]. intros a Ha.
assert (Ha' : 0 <= a < alloc_ceiling) by (clear - Ha Hf0 Hf1 Hac; destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]).
apply MEQ3; clear - Ha' Hsplo Hac; lia. }
first [exact Q19 | rewrite Q19; apply bv_eq; vm_compute; reflexivity].
+
rewrite branch_eq_U, (t2_cnt_U _ 40 (c_slct cx) 64), U_lit in Hc by (first [ew_havoc; exact HE40 | reflexivity | lia]).
assert (HsK : c_slct cx <> 64) by (destruct (Z.eqb_spec (3 * (64 - c_slct cx)) 0); [discriminate | lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJX PC_WDB.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (2%bv:reg) as Y2. jreg HS (18%bv:reg) as Y18. jreg HS (20%bv:reg) as Y20. jreg HS (21%bv:reg) as Y21. jreg HS (4%bv:reg) as Y4.
jreg HS (19%bv:reg) as Y19. jreg HS (9%bv:reg) as Y9.
rewrite ?ew_havoc_old in Y18 by (cbv; lia). rewrite HE44 in Y18.
pose proof (st_ok_reg _ _ _ _ (22%bv:reg) HS) as Y22. eval_sr_get_in Y22.
rewrite (t2_cnt_denot _ 40 (c_slct cx) 64) in Y22 by (first [ew_havoc; exact HE40 | reflexivity | lia]).
lazymatch type of HS with st_ok _ _ _ ?msx =>
cbn [ms_regs mkst] in Y2, Y18, Y20, Y21, Y22, Y19, Y9;
assert (MEQw : forall a, ~ (c_sp cx + 47 <= a < c_sp cx + 48) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs memX a)
by (intros a Hna Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H));
assert (Hobjw : objs_at (ms_mem msx) cx (c_rcur cx))
by (eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; rewrite MEQw by (clear - Hi Hcfplo Hcfphi Hsplo Hac Hraw0 Hraw1 Hg0 Hg1 HRSv HGSv; lia); [apply KX_cfg; exact Hi | apply (KX_blk _ _ i Hrawin2); clear - Hi Hraw0 Hraw1 Hrf HRSv HFBv; lia | apply (KX_blk _ _ i Hgin2); clear - Hi Hg0 Hg1 Hgf HGSv HFBv; lia]);
assert (HSKw : sink_at ubs0_msyms (ms_mem msx) mdX (c_f cx) (((S ++ ra_gce cx) ++ ra_hdr cx) ++ firstn (Z.to_nat (3 * c_slct cx)) LCTV))
by (apply (sink_at_frame ubs0_msyms memX _ mdX (c_f cx)); [| exact HSKX]; intros a Ha;
assert (Ha' : 0 <= a < alloc_ceiling) by (clear - Ha Hf0 Hf1 Hac; destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]);
apply MEQw; clear - Ha' Hsplo Hac; lia);
pose proof (fb_of_region _ _ _ _ _ _ _ _ 47 1%N (SLit 0) 0 (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) ltac:(ew_havoc; exact HE2) ltac:(cbv; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V47
end.
cbn [ms_mem mkst N.to_nat] in V47.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (rwdb_loop API IMG FWRITE (Z.to_nat (3 * (64 - c_slct cx))) (3 * (64 - c_slct cx)) _ _ RAWADD_STK (spZ regs0) _ _ _ _ _ _ _ _ (c_g cx) (c_gvals cx) (c_sp cx) (c_f cx));
[ rewrite Z2Nat.id by (clear - Hsk HsK Hnz F8; lia); reflexivity | clear - Hsk HsK Hnz F8; lia | exact HJX | exact (proj2 (proj2 Hobjw)) | exact Hwfn | exact Hfile | lia | lia | exact Hg16
| exact Hgin2 | exact Hfin2 | exact Hgf | exact Hf0 | exact Hf1 | intros a Ha; destruct Ha as (r & Hr & Har); exists r; split; [right; exact Hr | exact Har]
| rewrite Y2, <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HE2; reflexivity | exact Hspal | exact Hsplo
| clear - Hspe HSTKv HWv; lia | clear - Hspe; lia | clear - Hspe Hsp47; lia
| rewrite Y4, (HE 4%nat 4%bv eq_refl), R4, Htpv; reflexivity | exact Y18 | exact Y21 | exact Y20 | exact Y22 | exact V47 | exact HSKw | ].
rewrite !length_app, Lhdr.
rewrite (firstn_length_le LCTV HLn). unfold c_nP in Hroom. clear - Hroom Lgce Hsk Hnz Hw1 Hh1 F8. lia. }
cbv beta. intros c' (regs4 & mem4 & md4 & -> & HJ4 & HK4 & P21 & P22 & Hout4 & Hblk4 & HSK4).
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 27]%bv HS ltac:(apply env_agree_havoc_ge; [cbv; lia | apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]]) ltac:(vm_compute; reflexivity)) as HKw.
cbn [ms_regs mkst] in HKw.
assert (HK4' : forall r : reg, In r ([2; 3; 4; 8; 27]%bv : list reg) -> getr regs4 r = getr regs2 r).
{ intros r Hr. rewrite HK4 by (cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr). apply HKw. exact Hr. }
assert (K4_stk : forall a, c_sp cx <= a < c_sp cx + 144 -> ~ (c_sp cx + 47 <= a < c_sp cx + 48) -> mbyte ubs0segs mem4 a = mbyte ubs0segs mem2 a)
by (clear - Hout4 MEQw KX_stk Hsplo Hac Hsp47 HWv; intros a H1 H2; etransitivity; [apply (Hout4 a ltac:(lia) ltac:(lia))|]; rewrite MEQw by lia; apply KX_stk; lia).
assert (K4_blk : forall b n i, In (b, n) (blocks L2 A2) -> b + n <= alloc_ceiling -> 4096 <= b -> (b + n <= c_f cx \/ c_f cx + FILE_BLOCK <= b) -> 0 <= i < n ->
mbyte ubs0segs mem4 (b + i) = mbyte ubs0segs mem2 (b + i))
by (clear - Hblk4 MEQw KX_blk Hsplo Hac HFBv; intros b n i Hin Hhi Hlo Hsep Hi; etransitivity; [apply (Hblk4 b n i Hin Hi); intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia|];
rewrite MEQw by lia; apply (KX_blk b n i Hin Hhi Hlo Hsep Hi)).
assert (Hobjs4 : objs_at mem4 cx (c_rcur cx))
by (eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; [| apply (K4_blk _ _ i Hrawin2); clear - Hi Hraw0 Hraw1 Hrf HRSv HFBv; lia | apply (K4_blk _ _ i Hgin2); clear - Hi Hg0 Hg1 Hgf HGSv HFBv; lia];
rewrite (Hout4 (c_cfp cx + i)) by lia; rewrite MEQw by lia; apply KX_cfg; exact Hi).
remember (Ereg regs4 (ra_extra cx (c_rcur cx) [bb; M'])) as E4 eqn:HE4.
assert (HE' : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E4 n = getr regs4 rr) by (intros; subst E4; apply ew_Ereg_nat; assumption).
pose proof (E_rv regs4 cx (c_rcur cx) [bb; M']) as HY4. rewrite <- HE4 in HY4.
pose proof (E_morev regs4 cx (c_rcur cx) [bb; M'] LG) as HMo4. rewrite <- HE4 in HMo4.
assert (X2 : bv_unsigned (ew E4 2) = c_sp cx) by (rewrite (HE' 2%nat 2%bv eq_refl), (HK4' 2%bv) by (cbv; tauto); rewrite R2; apply unsigned_lit_small; lia).
assert (X44 : ew E4 44 = Z_to_bv 64 (c_g cx)) by (apply (HY4 1%nat); reflexivity).
assert (X69 : ew E4 69 = Z_to_bv 64 bb) by (apply (HMo4 0%nat); reflexivity).
assert (X70 : ew E4 70 = Z_to_bv 64 M') by (apply (HMo4 1%nat); reflexivity).
assert (HS4 : st_ok ubs0segs E4 ssWX (mkst regs4 (Z_to_bv 64 PC_WDBX) mem4 (seg_rom ubs0segs))).
{ rewrite HE4. unfold ssWX.
apply (ra_st_ok3W cx (c_rcur cx) regs4 [bb; M'] mem4 PC_WDBX _ 0 0 false _ _ [] [] Hcx Hobjs4); rewrite <- ?HE4.
- rewrite (HK4' 2%bv) by (cbv; tauto). exact R2.
- rewrite (HK4' 8%bv) by (cbv; tauto). exact R8.
- rewrite HE4. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[ apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite (HK4 9%bv) by (vm_compute; reflexivity); first [exact Y9 | rewrite Y9; apply bv_eq; vm_compute; reflexivity]]
| intros X; discriminate X | cbn [sv_denot]; rewrite (HK4 19%bv) by (vm_compute; reflexivity); first [exact Y19 | rewrite Y19; apply bv_eq; vm_compute; reflexivity]]
| intros X; discriminate X | cbn [sv_denot]; exact P21].
- intros a Ha. lia.
- intros X. discriminate X.
- reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite X69, unsigned_lit_small, Z.add_0_r by (clear - Hbb0 Hbb1 Hac HM; lia); reflexivity | cbn; clear - Hbb0 Hbb1 Hac HM; lia | cbn; lia | apply val_mem_word_mem; eapply fb_kept1; [apply val_mem_word_mem; exact W32 | intros a Ha; cbn in Ha; apply K4_stk; lia]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite X70, unsigned_lit_small, Z.add_0_r by (clear - HM'; lia); reflexivity | cbn; clear - HM'; lia | cbn; lia | eapply fb_kept1; [exact W40' | intros a Ha; cbn in Ha; apply K4_stk; lia]].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X70, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 PC_WDBX) mem4 (seg_rom ubs0segs))) in HJ4.
jrun_to LAWS ubs0tbl_ok HS4 HJ4 PC_T3; [eapply ra_wr_ok3W; [exact X2 | lia | lia | intros X; lia | left; cbn; lia] |].
pose proof (regs_kept_of_st_ok _ _ _ _ regs4 _ [2; 3; 4; 8; 27]%bv HS4 ltac:(rewrite HE4; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK5.
lazymatch type of HS4 with st_ok _ _ _ ?msx =>
cbn [ms_regs mkst] in HK5;
assert (MEQ3 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem4 a) by (intros a Ha; mbyte_chain ltac:(fun H => rewrite ?X2 in H));
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS4 eq_refl) as HRF;
assert (KF_stk : forall a, c_sp cx <= a < c_sp cx + 144 -> ~ (c_sp cx + 47 <= a < c_sp cx + 48) -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem2 a)
by (clear - MEQ3 K4_stk Hsplo Hac Hsp47; intros a H1 H2; rewrite MEQ3 by lia; apply K4_stk; lia);
assert (KF_blk : forall b n i, In (b, n) (blocks L2 A2) -> b + n <= alloc_ceiling -> 4096 <= b -> (b + n <= c_f cx \/ c_f cx + FILE_BLOCK <= b) -> 0 <= i < n ->
mbyte ubs0segs (ms_mem msx) (b + i) = mbyte ubs0segs mem2 (b + i))
by (clear - MEQ3 K4_blk Hsplo Hac; intros b n i Hin Hhi Hlo Hsep Hi; rewrite MEQ3 by lia; apply (K4_blk b n i Hin Hhi Hlo Hsep Hi))
end.
jreg HS4 (18%bv:reg) as Q18. rewrite X44 in Q18. jreg HS4 (20%bv:reg) as Q20. jreg HS4 (19%bv:reg) as Q19.
rewrite (st_ok_mkst _ _ _ _ HS4 eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- at_T3 _ _ _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) =>
exists L2, A2, (ms_regs msx), (ms_mem msx), md4, bb, Lbb, M end.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hid|]. split; [exact HRB|].
cbn [ms_regs ms_mem mkst] in *.
split; [rewrite HK5 by (cbv; tauto); rewrite HK4' by (cbv; tauto); exact R2|]. split; [rewrite HK5 by (cbv; tauto); rewrite HK4' by (cbv; tauto); exact R8|].
split; [rewrite HK5 by (cbv; tauto); rewrite HK4' by (cbv; tauto); rewrite R4, Htpv; reflexivity|]. split; [rewrite HK5 by (cbv; tauto); rewrite HK4' by (cbv; tauto); exact R3|].
split; [rewrite HK5 by (cbv; tauto); rewrite HK4' by (cbv; tauto); exact R27|].
split; [exact Q18|]. split; [exact Q20|].
split; [exact HB2|]. split; [exact Hwt|].
split. { apply val_mem_word_mem. eapply (fb_of_region _ _ _ _ _ _ _ _ 8 8%N (SOff 69%nat 0) bb HRF); [exact X2 | cbv; tauto | cbn [sv_denot]; rewrite X69, unsigned_lit_small, Z.add_0_r by (clear - Hbb0 Hbb1 Hac HM; lia); reflexivity | cbn; clear - Hbb0 Hbb1 Hac HM; lia | cbn; lia]. }
split. { change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)) in W40'. apply (proj2 (val_mem_mod _ _ _ _)). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). fold M'.
eapply (fb_of_region _ _ _ _ _ _ _ _ 16 4%N (SOff 70%nat 0) M' HRF); [exact X2 | cbv; tauto | cbn [sv_denot]; rewrite X70, unsigned_lit_small, Z.add_0_r by (clear - HM'; lia); reflexivity | cbn; clear - HM'; lia | cbn; lia]. }
split; [exact HM|].
split. { eapply objs_at_kept; [exact Hobjs4 | | |]; intros i Hi; apply MEQ3; lia. }
split. { eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]. intros a Ha. apply KF_stk; clear - Ha Hspe; lia. }
split. { destruct HVOK as (out & Hout & HGout & HMout). exists out. split; [exact Hout|]. split; [|exact HMout].
apply (garr8_frame ubs0segs mem2 _ bb out HGout). intros a Ha. rewrite <- HMout in Ha. replace a with (bb + (a - bb)) by lia. apply (KF_blk _ _ (a - bb) Hbbin); clear - Ha Hbb0 Hbb1 Hbf HM; lia. }
split; [exact HM2|].
split. { eapply fb_kept1; [exact (proj1 HFBC) | intros a Ha; cbn in Ha; apply KF_stk; clear - Ha Hspe; lia]. }
replace (ra_lctb cx LCTV) with (firstn (Z.to_nat (3 * c_slct cx)) LCTV ++ repeat 0 (Z.to_nat (3 * (64 - c_slct cx)))).
2:{ unfold ra_lctb, YO07.zeros. replace (c_slct cx =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). cbn [negb]. rewrite <- Hpp, Hp.
rewrite (Z.mod_small _ 65536) by (clear - Hsk Hnz F8; cbn; lia). f_equal; [f_equal; lia | f_equal; lia]. }
split. { rewrite <- !app_assoc in HSK4.
apply (sink_at_frame ubs0_msyms mem4 _ md4 (c_f cx)); [| exact HSK4]. intros a Ha.
assert (Ha' : 0 <= a < alloc_ceiling) by (clear - Ha Hf0 Hf1 Hac; destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]).
apply MEQ3; clear - Ha' Hsplo Hac; lia. }
first [exact Q19 | rewrite Q19; apply bv_eq; vm_compute; reflexivity].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
