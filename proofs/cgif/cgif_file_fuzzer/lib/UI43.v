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
UI4l UI3w UI4j UI4i UI4k UI4g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w UI2v UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma t2_x_U : forall E n s K c1 m2, ew E n = Z_to_bv 64 s -> 0 <= s <= K -> K <= 256 -> c1 = 2 * K -> m2 = -2 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m2)) (SLit c1)) = 2 * (K - s).
Proof using.
intros E n s K c1 m2 Hn Hs HK -> ->.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_SLit _ (-2)), (U_atom _ n s Hn), (U_lit _ (2 * K)) by lia.
change (zcanon (-2)) with 18446744073709551614. unfold zcanon, M64.
rewrite Zplus_mod_idemp_l. replace (s * 18446744073709551614 + 2 * K) with (2 * (K - s) + s * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma t2_y_U : forall E n s K c2, ew E n = Z_to_bv 64 s -> 0 <= s <= K -> K <= 256 -> c2 = - K ->
U E (SAlu ALU_SUB (SLit 0) (SOff n c2)) = K - s.
Proof using.
intros E n s K c2 Hn Hs HK ->.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, (U_lit _ 0), Hn, unsigned_lit_small by lia. unfold zcanon, M64.
rewrite Zminus_mod_idemp_r. replace (0 - (s + - K)) with (K - s) by lia. apply Z.mod_small. lia.
Qed.
Lemma t2_z_U : forall E n s K c3 m3, ew E n = Z_to_bv 64 s -> 0 <= s <= K -> K <= 256 -> c3 = 3 * K -> m3 = 18446744073709551613 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m3)) (SLit c3)) = 3 * (K - s).
Proof using.
intros E n s K c3 m3 Hn Hs HK -> ->.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom _ n s Hn), !U_lit by lia. unfold zcanon, M64.
rewrite Zplus_mod_idemp_l. replace (s * 18446744073709551613 + 3 * K) with (3 * (K - s) + s * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma t2_chk_ne : forall E n s K c1 c2 c3 m2 m3, ew E n = Z_to_bv 64 s -> 1 <= s <= K -> K <= 256 ->
c1 = 2 * K -> c2 = - K -> c3 = 3 * K -> m2 = -2 -> m3 = 18446744073709551613 ->
negb (U E (SAluw ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m2)) (SLit c1)) (SAlu ALU_SUB (SLit 0) (SOff n c2))) =?
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m3)) (SLit c3))) = false.
Proof using.
intros E n s K c1 c2 c3 m2 m3 Hn Hs HK H1 H2 H3 H4 H5.
rewrite (t2_z_U E n s K c3 m3 Hn ltac:(lia) HK H3 H5).
rewrite U_of_S, S_SAluw, (t2_x_U E n s K c1 m2 Hn ltac:(lia) HK H1 H4), (t2_y_U E n s K c2 Hn ltac:(lia) HK H2). cbn [zalu_raw].
rewrite !Z.mod_small by lia. rewrite swrap32_id by lia. rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
apply negb_false_iff, Z.eqb_eq. lia.
Qed.
Lemma t2_cnt_U : forall E n s K c m, ew E n = Z_to_bv 64 s -> 0 <= s <= K -> K <= 256 -> c = 3 * K * 2 ^ 48 -> m = 18446744073709551613 * 2 ^ 48 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m)) (SLit c)) (SLit 48)) = 3 * (K - s).
Proof using.
intros E n s K c m Hn Hs HK -> ->.
assert (HP : 2 ^ 48 = 281474976710656) by reflexivity.
assert (H1 : U E (SMd M_MUL (SOff n 0) (SLit (18446744073709551613 * 2 ^ 48))) = (s * (2 ^ 64 - 3 * 2 ^ 48)) mod 2 ^ 64).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom _ n s Hn) by lia. rewrite U_SLit. unfold zcanon, M64.
replace ((18446744073709551613 * 2 ^ 48) mod 2 ^ 64) with (2 ^ 64 - 3 * 2 ^ 48) by (vm_compute; reflexivity). reflexivity. }
assert (H2 : U E (SLit (3 * K * 2 ^ 48)) = 3 * K * 2 ^ 48) by (apply U_lit; rewrite HP; lia).
assert (H3 : U E (SLit 48) = 48) by (apply U_lit; lia).
rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SAlu. cbn [zalu_raw].
rewrite H1.
rewrite H2.
rewrite H3.
unfold zcanon, M64. rewrite Zplus_mod_idemp_l.
replace (s * (2 ^ 64 - 3 * 2 ^ 48) + 3 * K * 2 ^ 48) with (3 * (K - s) * 2 ^ 48 + s * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. rewrite (Z.mod_small (3 * (K - s) * 2 ^ 48)) by (rewrite ?HP; lia).
change (Z.land 48 63) with 48. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by (rewrite ?HP; lia). apply Z.mod_small. lia.
Qed.
Lemma t2_cnt_denot : forall E n s K c m, ew E n = Z_to_bv 64 s -> 0 <= s <= K -> K <= 256 -> c = 3 * K * 2 ^ 48 -> m = 18446744073709551613 * 2 ^ 48 ->
sv_denot E (SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m)) (SLit c)) (SLit 48)) = Z_to_bv 64 (3 * (K - s)).
Proof using.
intros E n s K c m Hn Hs HK Hc Hm. rewrite denot_lit_U. f_equal. exact (t2_cnt_U E n s K c m Hn Hs HK Hc Hm).
Qed.
Definition ssT2n : sstate :=
ra_ssW PC_T2 (sr_set (sr_set sr_atoms 23%bv (SLit 0)) 19%bv (SLit 0)) 47 48 enc_chunks false [(70%nat, mkAF 0 (2^32-1) 0)] [] [].
Definition ssT2l (p k : Z) : sstate :=
ra_ssW PC_T2 (sr_set (sr_set (sr_set sr_atoms 24%bv (SLit p)) 22%bv (SOff 9 30)) 19%bv (SLit 0)) 47 48 enc_chunks false
[(23%nat, mkAF 1 k 0); (40%nat, mkAF 1 k 0); (70%nat, mkAF 0 (2^32-1) 0)] [] [].
Definition ssWX : sstate :=
ra_ss3W PC_WDBX (sr_set (sr_set (sr_set sr_atoms 9%bv (SLit 0)) 19%bv (SLit 0)) 21%bv (SLit 0)) 0 0
enc_chunks false [(70%nat, mkAF 0 (2^32-1) 0)] [] [].
End d.
Ltac wrW HE2 := eapply ra_wr_okW; [exact HE2 | lia | lia | intros X; lia | left; cbn; lia].
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Variables (IMGV LCTV : list Z).
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Lemma ra_t2_nolct :
forall cx L A mem md L2 A2 md2 (regs0 regs2 : bvmap 5 word) (mem2 : word -> option byte) (p bb Lbb M : Z) (S : list Z) (b : rbound),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs0_msyms MR RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) L A mem md L2 A2 mem2 md2 ->
st_init_done A2 = true -> ra_rb b A2 Lbb -> Permutation (blocks L A) (c_blocks cx) ->
ra_regs regs2 cx -> getr regs2 23 = Z_to_bv 64 (c_slct cx) -> getr regs2 24 = Z_to_bv 64 p -> c_slct cx = 0 ->
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) ->
wtok' RAWADD_STK (spZ regs0) ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) (blocks L A) (bb, Lbb) ->
word_mem ubs0segs mem2 (c_sp cx + 8) bb -> val_mem ubs0segs mem2 (c_sp cx + 16) 4 M -> 1 <= M <= Lbb ->
objs_at mem2 cx (c_rcur cx) -> frame_savedN ubs0_msyms 12 regs0 mem2 (spZ regs0) ->
getr regs2 19 = Z_to_bv 64 0 ->
lzw_vok (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) mem2 bb M -> M <= 2 * c_nP cx + 16 -> fbC mem2 cx ->
sink_at ubs0_msyms mem2 md2 (c_f cx) (S ++ ra_gce cx) -> Z.of_nat (length S) + 2 * c_nP cx + 2048 <= SINK_MAX ->
SR ubs0segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs0segs)) md2)
(at_T3 API IMGV LCTV cx L A mem md regs0 S b).
Proof using FWRITE IMG.
intros cx L A mem md L2 A2 md2 regs0 regs2 mem2 p bb Lbb M S b Hcx HO HJ Hid HRB HB HR G23 G24 Hz HB2 Hwt W32 W40 HM Hobjs HFS G19 HVOK HM2 HFBC HSK Hroom.
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
assert (HE40 : ew E 40 = Z_to_bv 64 (c_slct cx)) by (apply (HX 8%nat); reflexivity).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE69 : ew E 69 = Z_to_bv 64 bb) by (apply (HMo 0%nat); reflexivity).
assert (HE70 : ew E 70 = Z_to_bv 64 M') by (apply (HMo 1%nat); reflexivity).
assert (HS : st_ok ubs0segs E ssT2n (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs0segs))).
{ subst E. unfold ssT2n.
apply (ra_st_okW cx (c_rcur cx) regs2 [bb; M'] mem2 PC_T2 _ 47 48 false _ _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite G23, Hz; reflexivity] | intros X; discriminate X | cbn [sv_denot]; exact G19].
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W32].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact W40'].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE70, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor.
}
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_writecb; [wrW HE2|].
assert (HWv : WRITECB_STK = 528) by reflexivity. assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE35 : ew E 35 = Z_to_bv 64 (c_w cx)) by (apply (HX 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 (c_h cx)) by (apply (HX 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 (c_top cx)) by (apply (HX 5%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 (c_left cx)) by (apply (HX 6%nat); reflexivity).
assert (HE32 : ew E 32 = Z_to_bv 64 (c_lct cx)) by (apply (HX 0%nat); reflexivity).
assert (Rpk : 0 <= ra_packed cx < 256).
{ unfold ra_packed. rewrite (proj2 (Z.eqb_eq _ _) Hz). cbn [negb]. destruct (YO07.flag (c_fattr cx) 2); lia. }
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
jrun_to LAWS ubs0tbl_ok HS HJW PC_T3.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 27]%bv HS ltac:(apply env_agree_havoc_ge; [cbv; lia | rewrite HE0; apply env_agree_refl]) ltac:(vm_compute; reflexivity)) as HKF.
lazymatch type of HS with st_ok _ _ _ ?msx =>
cbn [ms_regs mkst] in HKF;
assert (MEQ3 : forall a, ~ (c_sp cx + 47 <= a < c_sp cx + 48) -> 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs memW a)
by (intros a Hna Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H));
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HRF;
assert (KF_stk : forall a, c_sp cx <= a < c_sp cx + 144 -> ~ (c_sp cx + 47 <= a < c_sp cx + 48) -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem2 a)
by (clear - MEQ3 KW_stk Hsplo Hac Hsp47; intros a H1 H2; rewrite MEQ3 by lia; apply KW_stk; lia);
assert (KF_cfg : forall i, 0 <= i < 40 -> mbyte ubs0segs (ms_mem msx) (c_cfp cx + i) = mbyte ubs0segs mem2 (c_cfp cx + i))
by (clear - MEQ3 KW_cfg Hsplo Hac Hsp47 Hcfplo Hcfphi; intros i Hi; rewrite MEQ3 by lia; apply KW_cfg; lia);
assert (KF_blk : forall b n i, In (b, n) (blocks L2 A2) -> b + n <= alloc_ceiling -> 4096 <= b -> (b + n <= c_f cx \/ c_f cx + FILE_BLOCK <= b) -> 0 <= i < n ->
mbyte ubs0segs (ms_mem msx) (b + i) = mbyte ubs0segs mem2 (b + i))
by (clear - MEQ3 KW_blk Hsplo Hac; intros b n i Hin Hhi Hlo Hsep Hi; rewrite MEQ3 by lia; apply (KW_blk b n i Hin Hhi Hlo Hsep Hi))
end.
jreg HS (18%bv:reg) as Q18. rewrite ?ew_havoc_old in Q18 by (cbv; lia). rewrite HE44 in Q18.
jreg HS (20%bv:reg) as Q20. jreg HS (19%bv:reg) as Q19.
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- at_T3 _ _ _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) =>
exists L2, A2, (ms_regs msx), (ms_mem msx), mdW, bb, Lbb, M end.
split; [reflexivity|]. split; [exact HJW|]. split; [exact Hid|]. split; [exact HRB|].
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
replace (ra_lctb cx LCTV) with (@nil Z) by (unfold ra_lctb; rewrite (proj2 (Z.eqb_eq _ _) Hz); reflexivity). rewrite app_nil_r.
split. { rewrite <- !app_assoc in HSKW.
apply (sink_at_frame ubs0_msyms memW _ mdW (c_f cx)); [| exact HSKW]. intros a Ha.
assert (Ha' : 0 <= a < alloc_ceiling) by (clear - Ha Hf0 Hf1 Hac; destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]).
apply MEQ3; clear - Ha' Hsplo Hac; lia. }
first [exact Q19 | rewrite Q19; apply bv_eq; vm_compute; reflexivity].
Qed.
End S.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
