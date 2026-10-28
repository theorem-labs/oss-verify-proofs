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
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI1v UI4l UI21 UI2m UI3t UI5o UI5l YI6b UI5n UI20 UI1d UI2l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2o UI2p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI2q UI2r UI2i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI2n YI2k UI2b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition fl_entry_chunks : list YP09.chunk :=
[ mkChunk (-8) (CVal 8 (SOff 1 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-32) (CVal 8 (SOff 18 0));
mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-56) (CVal 8 (SOff 21 0)); mkChunk (-64) (CVal 8 (SOff 22 0));
mkChunk (-72) (CVal 8 (SOff 23 0)); mkChunk (-80) (CVal 8 (SOff 24 0)); mkChunk (-88) (CVal 8 (SOff 25 0)); mkChunk (-96) (CVal 8 (SOff 26 0));
mkChunk (-104) (CVal 8 (SOff 27 0)) ].
Lemma fl_saved_word : forall E mem sp0 off n (regs : bvmap 5 word) (rr : reg),
chunk_ok ubs0segs E mem sp0 (mkChunk off (CVal 8 (SOff n 0))) -> ew E n = getr regs rr ->
forall a, a = sp0 + off -> word_mem ubs0segs mem a (bv_unsigned (getr regs rr)).
Proof using.
intros E mem sp0 off n regs rr Hc He a ->. apply val_mem_word_mem.
eapply (val_of_chunk_ok ubs0segs E mem sp0 off 8%N (SOff n 0)); [exact Hc | | cbn; apply u64_range_getr | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, He, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma fl_saved_of_entry : forall E (regs : bvmap 5 word) mem sp0 cs,
Forall (chunk_ok ubs0segs E mem sp0) cs ->
(forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
incl fl_entry_chunks cs ->
fl_saved_ok mem sp0 regs.
Proof using.
intros E regs mem sp0 cs Hcs HE Hincl j r Hr.
assert (Hj : (j < 13)%nat) by (apply (proj1 (nth_error_Some FL_SAVED j)); rewrite Hr; discriminate).
assert (Hc : chunk_ok ubs0segs E mem sp0 (nth j fl_entry_chunks (mkChunk 0 (CVal 8 (SLit 0))))).
{ apply (proj1 (Forall_forall _ _) Hcs). apply Hincl. apply nth_In. cbn. exact Hj. }
do 13 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; cbn [nth fl_entry_chunks] in Hc;
eapply (fl_saved_word E mem sp0 _ _ regs _ Hc); [apply HE; reflexivity | cbn; lia] |]).
cbn in Hj. lia.
Qed.
Definition ss_e (pz : bool) : sstate :=
mkSS ubs0_A_flushFrame (if pz then sr_set sr_atoms 12%bv (SLit 0) else sr_atoms)
[ YP09.mkRegion (Some 2%nat) (-272) 0 (-272) 0 [] ;
YP09.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG) ;
YP09.mkRegion (Some 11%nat) 0 40 20 24 (obj_chunks_gen LAY_Frame A_F []) ] None
(mkFacts ([(2%nat, mkAF (CEIL_MIN + FLUSH_STK) (2^63 - 1) 4); (10%nat, mkAF 4096 (CEIL_MAX - 96) 4); (11%nat, mkAF 4096 (CEIL_MAX - 40) 3)]
++ (if pz then [] else [(12%nat, mkAF 4096 CEIL_MAX 0)]) ++ fl_gfacts ++ fl_ffacts) [] []).
Lemma clr3_low32 : forall v, 0 <= v < 2 ^ 32 -> Z.land v (2 ^ 32 - 4) = YO07.clr v 3.
Proof using.
intros v Hv. unfold YO07.clr. change (2 ^ 32 - 4) with ((Z.lnot 3) mod 2 ^ 32).
apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
destruct (Z.ltb_spec k 32) as [Hlt|Hge].
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- assert (Hb : Z.testbit v k = false).
{ destruct (Z.eq_dec v 0) as [->|Hz]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. assert (Z.log2 v < 32) by (apply Z.log2_lt_pow2; lia). lia. }
rewrite Hb. reflexivity.
Qed.
Lemma clr_range32 : forall v m, 0 <= v < 2 ^ 32 -> 0 <= YO07.clr v m < 2 ^ 32.
Proof using.
intros v m Hv. unfold YO07.clr. rewrite Z.land_comm. pose proof (land_le (Z.lnot m) v ltac:(lia)). lia.
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis RAWADDX : rawadd_specX API.
Hypothesis DIFFX : diff_specX API.
Theorem ubs0_flushFrame_x : flushX_spec API.
Proof using DIFFX IMG RAWADDX.
intros L A regs mem md g s N i f rest0 S GPAL cur bef brb HPRE Hid HSAT HSLEN HSP47 G10 Hat Hwf Hi Hf G11 G12 HB00 HGPAL XF XB XRA HRq HROOM.
set (rest := (cg_file s, FILE_BLOCK) :: rest0).
assert (HB : Permutation (blocks L A) (cgif_blocks0 g s N ++ rest)) by (subst rest; eapply Permutation_trans; [exact HB00 | apply cgif_blocks0_perm]).
set (G := gcfg_of s GPAL).
pose proof HPRE as (HH & Hra0 & Hst & Htp0 & Herr). destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
set (sp0 := spZ regs) in *.
set (FP := blocks_fp [(cg_raw s + 40, 4); (fr_ptr f + 20, 4)]).
assert (HFP : fl_fp FP s f).
{ split; intros a Ha; apply (proj2 (inFP_blocks_fp _ _)); [exists (cg_raw s + 40), 4 | exists (fr_ptr f + 20), 4]; split; [left; reflexivity | clear - Ha; lia | right; left; reflexivity | clear - Ha; lia]. }
set (FPw := FP ++ sink_fp (cg_file s)).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & Hfwf).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
destruct (af_cgif_geom0 API L A mem md g s N _ HH HB) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg).
destruct (fl_img_geom0 API L A mem md g s N _ f HH HB Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
pose proof Hat as (Hobj & Hraw & Hfrs). pose proof (Hfrs f Hfin) as Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
pose proof (Rf 2%nat (fr_attr f) eq_refl) as Rfattr. pose proof (Rf 3%nat (fr_gen f) eq_refl) as Rfgen. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfattr, Rfgen.
assert (Hfblk : In (fr_ptr f, FRAME_SIZE) (blocks L A)).
{ apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. left. apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | left; reflexivity]. }
assert (Hp8 : fr_ptr f mod 8 = 0).
{ pose proof (heap_blocks_range _ _ LAWS L A mem md (fr_ptr f) FRAME_SIZE HH Hfblk ltac:(lia)) as (_ & _ & H16).
clear - H16. apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide; [lia|]. destruct H16 as [q Hq]. exists (q * 2). lia. }
set (E := fl_E regs regs s f None []).
pose proof (fl_HE regs regs s f None [] : forall n rr, _ -> ew E n = _) as HE.
pose proof (fl_HX regs regs s f None [] : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (fl_HF regs regs s f None [] : forall n j v, _ -> _ -> ew E n = _) as HFf.
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = g) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; clear - Hg0 Hg1 Hac HGSv; lia).
assert (HU11 : bv_unsigned (ew E 11) = fr_ptr f) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; clear - Hp0 Hp1 Hac HFRv; lia).
assert (HE64 : ew E 64 = Z_to_bv 64 (fr_attr f)) by (apply (HFf 64%nat 2%nat _ eq_refl eq_refl)).
assert (HE65 : ew E 65 = Z_to_bv 64 (fr_gen f)) by (apply (HFf 65%nat 3%nat _ eq_refl eq_refl)).
assert (HE50 : ew E 50 = Z_to_bv 64 (cg_attr s)) by (apply (HX 50%nat 5%nat _ eq_refl eq_refl)).
pose proof (Rg 5%nat (cg_attr s) eq_refl) as Rgattr. cbn [nth snd LAY_CGIF Z.of_N] in Rgattr.
pose proof XF as (XA1 & XA2 & XA3 & XA4 & XA5 & XA6 & XA7 & XVI & XVIl & HVlp).
assert (V10 : U E (SExt true 32 (SOff 64 0)) mod 2 ^ 32 = fr_attr f) by (apply (U_sext32_low E 64 (fr_attr f) HE64); clear - Rfattr; lia).
assert (V24 : U E (SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 4)) = Z.land (fr_attr f) 4).
{ rewrite U_and_slit. change (zcanon 4) with 4. rewrite <- land_low32_small, V10 by (clear; lia). reflexivity. }
assert (V19 : U E (SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 1)) = Z.land (fr_attr f) 1).
{ rewrite U_and_slit. change (zcanon 1) with 1. rewrite <- land_low32_small, V10 by (clear; lia). reflexivity. }
assert (V50 : U E (SAlu ALU_AND (SExt false 8 (SOff 50 0)) (SLit 8)) = Z.land (cg_attr s) 8).
{ rewrite U_and_lit by (clear; lia). rewrite U_zext, (U_atom _ 50 (cg_attr s) HE50) by (clear - Rgattr; lia).
change (2 ^ Z.of_N 8) with (2 ^ 8). rewrite <- Z.land_ones by (clear; lia). rewrite <- Z.land_assoc. f_equal. }
assert (V64_2 : U E (SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 2)) = Z.land (fr_attr f) 2).
{ rewrite U_and_slit. change (zcanon 2) with 2. rewrite <- land_low32_small, V10 by (clear; lia). reflexivity. }
assert (VOR : U E (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 50 0)) (SLit 8)) (SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 2))) = Z.lor (Z.land (cg_attr s) 8) (Z.land (fr_attr f) 2))
by (rewrite U_or_d, V50, V64_2; reflexivity).
assert (V25 : U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 50 0)) (SLit 8)) (SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 2)))) = (if fl_hasAlpha G cur then 1 else 0)).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, VOR. change (zcanon 0) with 0. unfold fl_hasAlpha, YO07.flag. cbn [YO07.g_attr G gcfg_of]. rewrite <- XA1.
pose proof (land_le (cg_attr s) 8 ltac:(clear; lia)) as L1. pose proof (land_le (fr_attr f) 2 ltac:(clear; lia)) as L2.
destruct (Z.eqb_spec (Z.land (cg_attr s) 8) 0) as [Z8|Z8]; destruct (Z.eqb_spec (Z.land (fr_attr f) 2) 0) as [Z2|Z2]; cbn [negb orb];
rewrite ?Z8, ?Z2; rewrite ?Z.lor_0_l, ?Z.lor_0_r.
- reflexivity.
- destruct (Z.ltb_spec 0 (Z.land (fr_attr f) 2)); [reflexivity | exfalso; clear - L2 Z2 H; lia].
- destruct (Z.ltb_spec 0 (Z.land (cg_attr s) 8)); [reflexivity | exfalso; clear - L1 Z8 H; lia].
- destruct (Z.ltb_spec 0 (Z.lor (Z.land (cg_attr s) 8) (Z.land (fr_attr f) 2))) as [Hl|Hl]; [reflexivity | exfalso].
pose proof (proj1 (Z.lor_eq_0_iff (Z.land (cg_attr s) 8) (Z.land (fr_attr f) 2))) as LZ.
pose proof (proj2 (Z.lor_nonneg (Z.land (cg_attr s) 8) (Z.land (fr_attr f) 2)) ltac:(clear - L1 L2; lia)) as LN.
destruct (LZ ltac:(clear - Hl LN; lia)) as [A1 A2]. exact (Z8 A1). }
assert (HSt : branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 4))) (sv_denot E (SLit 0)) = true -> fl_hasSet cur = true).
{ rewrite branch_ne_U, V24, U_lit by (clear; lia). unfold fl_hasSet, YO07.flag. rewrite <- XA1. intros Hb. exact Hb. }
assert (HSf : branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 4))) (sv_denot E (SLit 0)) = true -> fl_hasSet cur = false).
{ rewrite branch_eq_U, V24, U_lit by (clear; lia). unfold fl_hasSet, YO07.flag. rewrite <- XA1. intros Hb. rewrite Hb. reflexivity. }
assert (HAt : branch_taken BC_NE (sv_denot E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 50 0)) (SLit 8)) (SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 2))))) (sv_denot E (SLit 0)) = true -> fl_hasAlpha G cur = true).
{ rewrite branch_ne_U, V25, U_lit by (clear; lia). destruct (fl_hasAlpha G cur); [reflexivity | intros Hb; discriminate Hb]. }
assert (HAf : branch_taken BC_EQ (sv_denot E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 50 0)) (SLit 8)) (SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 2))))) (sv_denot E (SLit 0)) = true -> fl_hasAlpha G cur = false).
{ rewrite branch_eq_U, V25, U_lit by (clear; lia). destruct (fl_hasAlpha G cur); [intros Hb; discriminate Hb | reflexivity]. }
assert (U65 : U E (SOff 65 0) = fr_gen f) by (apply (U_atom _ 65 (fr_gen f) HE65); clear - Rfgen; lia).
assert (UEa : U E (SOff 65 0) mod 2 ^ 32 = fr_gen f) by (rewrite U65; apply Z.mod_small; clear - Rfgen; lia).
assert (UEb : U E (SAlu ALU_AND (SOff 65 0) (SLit (-4))) mod 2 ^ 32 = YO07.clr (fr_gen f) 3).
{ rewrite U_and_slit, land_mod_pow2, U65, (Z.mod_small (fr_gen f)) by (clear - Rfgen; lia). change (zcanon (-4) mod 2 ^ 32) with (2 ^ 32 - 4). apply clr3_low32. clear - Rfgen; lia. }
assert (UEc : U E (SAlu ALU_AND (SAlu ALU_AND (SOff 65 0) (SLit (-4))) (SLit (-2))) mod 2 ^ 32 = YO07.clr (YO07.clr (fr_gen f) 3) 1).
{ rewrite U_and_slit, land_mod_pow2, UEb by (clear; lia). change (zcanon (-2) mod 2 ^ 32) with (2 ^ 32 - 2). apply clr1_low32. apply clr_range32. clear - Rfgen; lia. }
assert (UEd : U E (SAlu ALU_AND (SOff 65 0) (SLit (-2))) mod 2 ^ 32 = YO07.clr (fr_gen f) 1).
{ rewrite U_and_slit, land_mod_pow2, U65, (Z.mod_small (fr_gen f)) by (clear - Rfgen; lia). change (zcanon (-2) mod 2 ^ 32) with (2 ^ 32 - 2). apply clr1_low32. clear - Rfgen; lia. }
assert (Hrawin : In (cg_raw s, RAW_SIZE) (blocks L A)) by (apply (Permutation_in _ (Permutation_sym HB00)); apply in_app_iff; left; unfold cgif_blocks; right; left; reflexivity).
assert (Hfilein : In (cg_file s, FILE_BLOCK) (blocks L A)) by (apply (Permutation_in _ (Permutation_sym HB00)); apply in_app_iff; left; unfold cgif_blocks; right; right; left; reflexivity).
assert (HBf : Permutation (blocks L A) ((cg_file s, FILE_BLOCK) :: cgif_blocks0 g s N ++ rest0)).
{ eapply Permutation_trans; [exact HB|]. subst rest. apply Permutation_sym. apply Permutation_middle. }
assert (SEPraw : cg_file s + FILE_BLOCK <= cg_raw s \/ cg_raw s + RAW_SIZE <= cg_file s)
by (exact (heap_sep_perm _ _ LAWS L A mem md (cg_file s, FILE_BLOCK) _ (cg_raw s, RAW_SIZE) HH HBf ltac:(apply in_app_iff; left; right; left; reflexivity))).
assert (SEPf : cg_file s + FILE_BLOCK <= fr_ptr f \/ fr_ptr f + FRAME_SIZE <= cg_file s)
by (exact (heap_sep_perm _ _ LAWS L A mem md (cg_file s, FILE_BLOCK) _ (fr_ptr f, FRAME_SIZE) HH HBf ltac:(apply in_app_iff; left; apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | left; reflexivity]))).
assert (HFPin : forall a, inFP FP a -> (cg_raw s + 40 <= a < cg_raw s + 44) \/ (fr_ptr f + 20 <= a < fr_ptr f + 24)).
{ intros a Hin. subst FP. apply (proj1 (inFP_blocks_fp _ _)) in Hin as (bb & nn & Hbn & Hab). destruct Hbn as [Hx | [Hx | []]]; injection Hx as <- <-; [left | right]; clear - Hab; lia. }
assert (HSINK : fl_sink g s N rest FP FPw S L A mem md sp0).
{ unfold fl_sink. split; [exact HSAT|]. split; [exact HSLEN|]. split; [exact HSP47|]. split; [exact Hfilein|]. split; [subst rest; left; reflexivity|].
split.
{ unfold sink_open_fp, in_fp. intros Hin. destruct (HFPin 0 Hin) as [X|X]; clear - X Hr0 Hp0; lia. }
split.
{ intros a Ha Hin. destruct (HFPin a Hin) as [X|X]; clear - X Ha SEPraw SEPf HRWv HFRv; lia. }
split; [intros a Hin; subst FPw; apply (proj2 (inFP_app _ _ _)); left; exact Hin|].
intros a Hin. subst FPw. apply (proj2 (inFP_app _ _ _)). right. exact Hin. }
clearbody FP.
assert (Hbfrj : nth (i - 1) (cg_frames s) None = None \/ exists j b', nth (i - 1) (cg_frames s) None = Some b' /\ nth_error (cg_frames s) j = Some (Some b') /\ j <> i).
{ destruct (nth (i - 1) (cg_frames s) None) as [b'|] eqn:Hn; [right | left; reflexivity]. exists (i - 1)%nat, b'. split; [reflexivity|]. split; [| clear - Hi; lia].
rewrite (nth_error_nth' _ None) by (clear - Hilt; lia). rewrite Hn. reflexivity. }
assert (VK : forall m, (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 272) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs0segs m a = mbyte ubs0segs mem a) ->
fl_vals m s N f (nth (i - 1) (cg_frames s) None) GPAL cur bef).
{ intros m K. eapply fl_vals_kept; [| split; [exact HGPAL | split; [exact XF | split; [exact XB | exact XRA]]]]. intros a0 n0 k Hin Hk.
assert (Hbn' : In (a0, n0) (blocks L A)).
{ apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. left. apply (fl_vblocks_sub g s N f (nth (i - 1) (cg_frames s) None) i Hf); [| exact Hin].
destruct Hbfrj as [-> | (j & b' & -> & Hj & _)]; [left; reflexivity | right; exists j; exact Hj]. }
destruct (blocks_range _ _ LAWS L A mem md a0 n0 HH Hbn') as [R0 R1].
pose proof (fl_vblocks_sep0 API L A mem md g s N rest i f (nth (i - 1) (cg_frames s) None) (a0, n0) HH HB Hf Hbfrj Hin) as X. cbn [fst snd] in X.
apply K; clear - R0 R1 Hk X Hceil HFSv HFRv Hac; lia. }
assert (Hpzb : (frame_ptr (nth (i - 1) (cg_frames s) None) = 0 -> bef = None) /\ (frame_ptr (nth (i - 1) (cg_frames s) None) <> 0 -> exists befr, bef = Some befr)).
{ generalize XB. unfold oframe_rel0, oframe_relb. destruct (nth (i - 1) (cg_frames s) None) as [b'|] eqn:Hn; destruct bef as [befr|]; intros XB'; try (exfalso; exact XB').
- split; [| intros _; exists befr; reflexivity]. intros Hz. exfalso.
assert (Hbin : In (Some b') (cg_frames s)) by (rewrite <- Hn; apply nth_In; clear - Hilt Hi; lia).
destruct (Hfgeom b' Hbin) as (Q0 & _). cbn [frame_ptr] in Hz. clear - Q0 Hz. lia.
- split; [intros _; reflexivity | intros Hz; exfalso; apply Hz; reflexivity]. }
pose proof (flush_room_notmp brb N ltac:(clear - HN HW1 HH1; nia) HROOM) as [HRR0 HRB0].
assert (HNUM : forall n, 0 < n <= N -> room brb n /\ rawadd_room (rb_malloc brb n) n /\ rb_le (rb_free (rawadd_rb (rb_malloc brb n)) n) (flush_rb brb))
by (intros n Hn; exact (flush_room_tmp brb N n ltac:(clear - HN HW1 HH1; nia) Hn HROOM)).
assert (HR0 : region_ok ubs0segs E mem (YP09.mkRegion (Some 2%nat) (-272) 0 (-272) 0 [])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia | apply Forall_nil]. }
assert (HR1 : region_ok ubs0segs E mem (YP09.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG))).
{ unfold fl_litsG, A_X. eapply (region_ok_obj_gen ubs0segs E mem 10 g 96 0 0 LAY_CGIF (cgif_vals s) 45 (litsG None None None None));
[exact HU10 | lia | lia | exact Hobj | reflexivity | | apply (litsG_ok s); exact I | intros k Hk; lia].
intros j v Hj. apply (HX (45 + j)%nat j v eq_refl Hj). }
assert (HR2 : region_ok ubs0segs E mem (YP09.mkRegion (Some 11%nat) 0 40 20 24 (obj_chunks_gen LAY_Frame A_F []))).
{ unfold A_F. eapply (region_ok_obj_gen ubs0segs E mem 11 (fr_ptr f) 40 20 24 LAY_Frame (frame_vals f) 62 []);
[exact HU11 | lia | lia | exact Hfobj | reflexivity | | intros [|j] z Hz; discriminate Hz | ].
- intros j v Hj. apply (HFf (62 + j)%nat j v eq_refl Hj).
- intros k Hk. apply (present_writable ubs0_msyms). apply (proj1 (heap_blocks _ _ LAWS L A mem md (fr_ptr f) FRAME_SIZE k HH Hfblk ltac:(clear - Hk HFRv; lia))). }
assert (HPD : forall pz, pairwise_disjoint E (ss_mem (ss_e pz))).
{ intros pz. cbn [ss_mem ss_e pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11. clear - Hg1 Hp1 Hpg Hceil HFSv HGSv HFRv Hac. repeat split; lia. }
pose proof (fl_gfacts_ok regs regs s f None [] mem g N Hobj Hwf ltac:(lia) ltac:(lia)) as HFAb.
assert (HimC : fr_img f <= alloc_ceiling) by (clear - Him1 HN HW1 HH1; nia).
pose proof (fl_ffacts_ok regs regs s f None [] mem (fr_ptr f) Hfobj Him0 HimC) as HFAc.
assert (HFAa : atoms_ok E [(2%nat, mkAF (CEIL_MIN + FLUSH_STK) (2^63 - 1) 4); (10%nat, mkAF 4096 (CEIL_MAX - 96) 4); (11%nat, mkAF 4096 (CEIL_MAX - 40) 3)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU10, HU11.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. clear - Hceil H63 Hal16 Hg0 Hg1 Hg16 Hp0 Hp1 Hp8 HFSv HGSv HFRv Hac. repeat split; lia. }
assert (HFAd : frame_ptr (nth (i - 1) (cg_frames s) None) <> 0 -> atoms_ok E [(12%nat, mkAF 4096 CEIL_MAX 0)]).
{ intros Hnz. destruct (nth (i - 1) (cg_frames s) None) as [b|] eqn:Hn; [| exfalso; apply Hnz; reflexivity].
assert (Hbin : In (Some b) (cg_frames s)) by (rewrite <- Hn; apply nth_In; lia).
destruct (Hfgeom b Hbin) as (Q0 & Q1 & _).
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (HE 12%nat 12%bv eq_refl), G12; try rewrite Hn. cbn [frame_ptr]. rewrite unsigned_lit_small by (clear - Q0 Q1 Hac HFRv; lia).
change (2 ^ 0) with 1. rewrite Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Q0 Q1 HFRv. repeat split; lia. }
assert (MK : forall pz : bool, (if pz then frame_ptr (nth (i - 1) (cg_frames s) None) = 0 else frame_ptr (nth (i - 1) (cg_frames s) None) <> 0) ->
st_ok ubs0segs E (ss_e pz) (mkst regs (Z_to_bv 64 ubs0_A_flushFrame) mem (seg_rom ubs0segs))).
{ intros pz Hpz. unfold ss_e. apply entry_st_ok_full; [| vm_compute; destruct pz; reflexivity | | exact (HPD pz) |].
- destruct pz; [| apply regs_ok_Ereg]. apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx |]. rewrite G12, Hpz. reflexivity.
- constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor.
- split; [| split; exact I]. apply atoms_ok_app; [exact HFAa|]. apply atoms_ok_app; [| apply atoms_ok_app; [exact HFAb | exact HFAc]].
destruct pz; [exact I | exact (HFAd Hpz)]. }
clear HR0 HR1 HR2 HPD HFAa HFAb HFAc HFAd.
pose proof (journal_init ubs0_msyms MR FLUSH_STK FP L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_flushFrame) mem (seg_rom ubs0segs))) in HJ. fold sp0 in HJ.
assert (WR : forall E0 cs fcs, bv_unsigned (ew E0 2) = sp0 -> bv_unsigned (ew E0 11) = fr_ptr f ->
wr_ok E0 [YP09.mkRegion (Some 2%nat) (-272) 0 (-272) 0 cs; YP09.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG);
YP09.mkRegion (Some 11%nat) 0 40 20 24 fcs] FLUSH_STK sp0 FP (blocks L A) (blocks L A)).
{ intros E0 cs fcs H2 H11. eapply wr_ok_cons_stack; [reflexivity | exact H2 | cbn; lia | cbn; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply (wr_ok_cons_block E0 (YP09.mkRegion (Some 11%nat) 0 40 20 24 fcs) [] FLUSH_STK sp0 FP (blocks L A) (blocks L A) 11 (fr_ptr f) FRAME_SIZE eq_refl H11 Hfblk); [cbn; lia | cbn; clear - HFRv; lia | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. exact (proj2 HFP a Ha). }
assert (KSTEP : forall E0 cs fcs (m m' : word -> option byte),
bv_unsigned (ew E0 2) = sp0 -> bv_unsigned (ew E0 11) = fr_ptr f ->
frame_of E0 [YP09.mkRegion (Some 2%nat) (-272) 0 (-272) 0 cs; YP09.mkRegion (Some 10%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG);
YP09.mkRegion (Some 11%nat) 0 40 20 24 fcs] m m' ->
forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 272) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs0segs m' a = mbyte ubs0segs m a).
{ intros E0 cs fcs m m' H2 H11 HFx a Ha Hn1 Hn2. apply (mbyte_of_frame _ _ _ _ a HFx Ha). intros r Hr. cbv [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?H2, ?H11; clear - Hn1 Hn2; lia |]). destruct Hr. }
assert (FRo : forall x j v rcur, nth_error (cg_frames s) j = Some (Some x) -> j <> i -> In (Some x) (cg_frames (flush_upd s i v rcur))).
{ intros x j v rcur Hj Hji. rewrite (cg_frames_flush_upd s i v rcur f Hf). eapply (nth_error_In _ j). rewrite nth_error_list_set_other by lia. exact Hj. }
assert (CGAT : forall (m : word -> option byte) (v : Z),
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 272) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs0segs m a = mbyte ubs0segs mem a) ->
field_ok ubs0segs m (fr_ptr f) (20, 4%N) v ->
cgif_at m g (flush_upd s i v (rw_cur s))).
{ intros m v K Hfld.
assert (KB : forall bb nn k, In (bb, nn) (cgif_blocks0 g s N) -> 0 <= k < nn -> (bb + nn <= fr_ptr f \/ fr_ptr f + FRAME_SIZE <= bb) ->
mbyte ubs0segs m (bb + k) = mbyte ubs0segs mem (bb + k)).
{ intros bb nn k Hbn Hk Hsep. assert (Hbn' : In (bb, nn) (blocks L A)) by (apply (Permutation_in _ (Permutation_sym HB)); apply in_app_iff; left; exact Hbn).
destruct (blocks_range _ _ LAWS L A mem md bb nn HH Hbn') as [R0 R1]. apply K; clear - R0 R1 Hk Hsep Hceil HFSv HFRv Hac; lia. }
split; [| split].
- rewrite (cgif_vals_flush_upd s i v (rw_cur s)). eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply (KB g CGIF_SIZE k); [left; reflexivity | clear - Hk HGSv; lia | clear - Hpg; lia]].
- change (cg_raw (flush_upd s i v (rw_cur s))) with (cg_raw s). change (raw_vals g (flush_upd s i v (rw_cur s))) with (raw_vals g s).
pose proof (af_raw_frame_sep0 API L A mem md g s N _ f HH HB Hfin) as Hrf.
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply (KB (cg_raw s) RAW_SIZE k); [right; left; reflexivity | clear - Hk HRWv; lia | clear - Hrf; lia]].
- intros x Hx. destruct (In_frames_flush_upd s i v (rw_cur s) f x Hf Hx) as [-> | [Hin (j & Hj & Hji)]].
+ change (fr_ptr (set_fr_gen f v)) with (fr_ptr f). rewrite frame_vals_set_fr_gen.
eapply (obj_at_upd ubs0segs mem m (fr_ptr f) LAY_Frame FRAME_SIZE (frame_vals f) _ [3%nat] [(20, 24)]);
[exact Hfobj | exact (proj1 LAY_Frame_ok) | reflexivity | reflexivity | | | ].
* intros k Hk Hw. apply K; [clear - Hk Hp0 Hp1 HFRv Hac; lia | clear - Hk Hp1 Hceil HFSv HFRv Hac; lia |].
cbn [in_wins existsb fst snd] in Hw. clear - Hk Hw. intros Hc.
assert (Hb1 : (20 <=? k) && (k <? 24) = true) by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). rewrite Hb1 in Hw. discriminate Hw.
* intros j0 fd v' Hj0 Hfd Hv'. destruct Hj0 as [<- | []]. cbn in Hfd, Hv'. injection Hfd as <-. injection Hv' as <-. exact Hfld.
* intros j0 Hj0. destruct (Nat.eq_dec j0 3) as [-> | Hne]; [exfalso; apply Hj0; left; reflexivity|].
do 9 (destruct j0 as [|j0]; [first [reflexivity | exfalso; lia] |]). reflexivity.
+ destruct (Hfgeom x Hin) as (X0 & X1 & _). pose proof (af_frames_sep0 API L A mem md g s N _ j i x f HH HB Hj Hf Hji) as Xf.
eapply obj_at_transport_range; [exact (Hfrs x Hin) | exact (proj1 LAY_Frame_ok) |].
intros k Hk. apply (KB (fr_ptr x) FRAME_SIZE k); [| clear - Hk HFRv; lia | clear - Xf; lia].
apply (frame_blocks_in_cgif0 g s N x _ _ Hin). left. reflexivity. }
assert (GO : forall ss ms' (e : sv) (pz ha hs : bool), st_ok ubs0segs E ss ms' -> ss_pc ss = FL_F2 -> ss_resv ss = None ->
(exists rg0 rg2, nth_error (ss_mem ss) 0 = Some rg0 /\ r_base rg0 = Some 2%nat /\ nth_error (ss_mem ss) 2 = Some rg2 /\ r_base rg2 = Some 11%nat /\
incl_chunks (fl_entry_chunks ++ [mkChunk (-160) (CVal 8 (SOff 10 0)); mkChunk (-152) (CVal 8 (SOff 11 0))]) (r_chunks rg0) = true /\
In (mkChunk 20 (CVal 4 e)) (r_chunks rg2)) ->
(if pz then frame_ptr (nth (i - 1) (cg_frames s) None) = 0 else frame_ptr (nth (i - 1) (cg_frames s) None) <> 0) ->
(pz = true -> Z.land (U E e) 3 = 0) ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [3; 4]%bv = true ->
sr_get (ss_regs ss) 2%bv = SOff 2 (-272) -> sr_get (ss_regs ss) 16%bv = SOff 11 0 ->
sr_get (ss_regs ss) 18%bv = (if pz then SLit 0 else SOff 12 0) ->
sr_get (ss_regs ss) 12%bv = SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 1) ->
sr_get (ss_regs ss) 27%bv = SOff 52 0 -> sr_get (ss_regs ss) 19%bv = SOff 53 0 ->
sr_get (ss_regs ss) 10%bv = SExt true 32 (SOff 64 0) -> sr_get (ss_regs ss) 13%bv = SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 4) ->
sr_get (ss_regs ss) 15%bv = SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 50 0)) (SLit 8)) (SAlu ALU_AND (SExt true 32 (SOff 64 0)) (SLit 2))) ->
(if pz then True else fl_hasAlpha G cur = ha) -> fl_hasSet cur = hs ->
U E e mod 2 ^ 32 = (if hs then YO07.clr (if pz || ha then YO07.clr (fr_gen f) 3 else fr_gen f) 1 else (if pz || ha then YO07.clr (fr_gen f) 3 else fr_gen f)) ->
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md L A (ms_mem ms') md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 272) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs mem a) ->
SR ubs0segs (mkCfg ms' md) (fl_post API regs g s N i rest FPw S GPAL cur bef brb L A mem md)).
{ intros ss ms' e pz ha hs HS' Hpc Hrv (rg0 & rg2 & Hrg0 & Hb0 & Hrg2 & Hb2 & Hincl & Hin20) Hpz He3 Hkl Q2 Q16 Q18 Q12 Q27 Q19 Q10 Q13 Q15 Hha Hhs He HJ' K.
assert (Xgena : U E e mod 2 ^ 32 = fl_gen2 G cur bef).
{ rewrite He. unfold fl_gen2, fl_gen1. rewrite Hhs, <- XA2. destruct pz.
- rewrite (proj1 Hpzb Hpz). reflexivity.
- destruct (proj2 Hpzb Hpz) as [befr ->]. rewrite Hha. reflexivity. }
pose proof (regs_kept_of_st_ok ubs0segs _ ss ms' regs _ _ HS' (env_agree_refl _ _) Hkl) as R.
pose proof (st_region_chunks ubs0segs E ss ms' 0 rg0 2%nat sp0 HS' Hrg0 Hb0 HU2) as Hcs0.
apply incl_chunks_sound in Hincl.
assert (CW : forall off e0 v, In (mkChunk off (CVal 8 e0)) [mkChunk (-160) (CVal 8 (SOff 10 0)); mkChunk (-152) (CVal 8 (SOff 11 0))] ->
sv_denot E e0 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> word_mem ubs0segs (ms_mem ms') (sp0 + off) v).
{ intros off e0 v Hin Hd Hv. apply (chunk_word E _ _ off e0 v); [| exact Hd | exact Hv].
apply (proj1 (Forall_forall _ _) Hcs0). apply Hincl. apply in_app_iff. right. exact Hin. }
assert (RGx : forall (r : reg) sv, sr_get (ss_regs ss) r = sv -> getr (ms_regs ms') r = sv_denot E sv).
{ intros r sv Hr. rewrite (st_ok_reg ubs0segs E ss ms' r HS'), Hr. reflexivity. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc.
eapply (fl_f2 API IMG RAWADDX DIFFX L A mem md regs (ms_regs ms') L A (ms_mem ms') md g N s i f (U E e mod 2 ^ 32) rest FP FPw S GPAL cur (nth (i - 1) (cg_frames s) None) bef brb
(if fl_hasAlpha G cur then 1 else 0));
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hi | exact Hf | | apply Z.mod_pos_bound; clear; lia | exact HFP | exact HB | | | | | | | | | |
| reflexivity | exact HSINK | apply VK; exact K
| rewrite (RGx _ _ Q10); exact V10
| rewrite (RGx _ _ Q13); apply denot_of_U'; exact V24
| rewrite (RGx _ _ Q15); apply denot_of_U'; exact V25
| reflexivity | exact Xgena | exact HNUM | exact HRR0 | exact HRB0 | exact HRq ].
- apply (CGAT (ms_mem ms') (U E e mod 2 ^ 32) K).
eapply (st_field_low ubs0segs E ss ms' 2 rg2 11 (fr_ptr f) 20 4 e (2 ^ 32) HS' Hrg2 Hb2 Hin20 HU11 ltac:(cbn; lia) eq_refl).
- intros Hn. rewrite land3_mod32 by (apply U_range). apply He3. destruct pz; [reflexivity | exfalso; apply Hpz; rewrite Hn; reflexivity].
- eapply (fl_saved_of_entry E regs (ms_mem ms') sp0 (r_chunks rg0) Hcs0 HE). intros c Hc. apply Hincl. apply in_app_iff. left. exact Hc.
- rewrite (RGx _ _ Q2). cbn [sv_denot]. rewrite HU2. reflexivity.
- fold sp0. replace (sp0 - 272 + 112) with (sp0 + -160) by lia.
apply (CW (-160) (SOff 10 0)); [left; reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity | clear - Hg0 Hg1 Hac HGSv; lia].
- fold sp0. replace (sp0 - 272 + 120) with (sp0 + -152) by lia.
apply (CW (-152) (SOff 11 0)); [right; left; reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, HU11; reflexivity | clear - Hp0 Hp1 Hac HFRv; lia].
- rewrite (RGx _ _ Q16). cbn [sv_denot]. rewrite Z.add_0_r, HU11. reflexivity.
- rewrite (RGx _ _ Q18). destruct pz; [rewrite Hpz; reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 12%nat 12%bv eq_refl); exact G12].
- rewrite (RGx _ _ Q12). apply denot_of_U'. rewrite U_and_slit. change (zcanon 1) with 1.
replace (Z.land (U E (SExt true 32 (SOff 64 0))) 1) with (Z.land (Z.land (U E (SExt true 32 (SOff 64 0))) 3) 1) by (rewrite <- Z.land_assoc; reflexivity).
rewrite land3_sext32, (U_atom _ 64 (fr_attr f) HE64) by (clear - Rfattr; lia). rewrite <- Z.land_assoc. reflexivity.
- rewrite (RGx _ _ Q27). cbn [sv_denot]. rewrite Z.add_0_r, (HX 52%nat 7%nat _ eq_refl eq_refl), unsigned_lit_small by (clear - RW; lia). reflexivity.
- rewrite (RGx _ _ Q19). cbn [sv_denot]. rewrite Z.add_0_r, (HX 53%nat 8%nat _ eq_refl eq_refl), unsigned_lit_small by (clear - RH; lia). reflexivity.
- split; [rewrite (R 3%bv ltac:(cbv; auto 50)); reflexivity | rewrite (R 4%bv ltac:(cbv; auto 50)); reflexivity]. }
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 272) -> ~ (fr_ptr f + 20 <= a < fr_ptr f + 24) -> mbyte ubs0segs mem a = mbyte ubs0segs mem a) by (intros; reflexivity).
Ltac kstep3 KSTEP HU2 HU11 :=
let HF := get_HF in cbn [ms_mem mkst] in HF; clear_HG;
lazymatch goal with K : forall a, _ -> _ -> _ -> mbyte ubs0segs ?m a = mbyte ubs0segs ?m0 a |- _ =>
lazymatch type of HF with frame_of ?E1 ?rs m ?m2 =>
let K2 := fresh "K" in
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (_ <= a < _) -> ~ (_ <= a < _) -> mbyte ubs0segs m2 a = mbyte ubs0segs m0 a)
by (intros a Ha Hn1 Hn2; try rewrite <- (K a Ha Hn1 Hn2); exact (KSTEP E1 _ _ m m2 HU2 HU11 HF a Ha Hn1 Hn2));
clear HF K
end
end.
eapply SR_mono.
{ destruct (Z.eq_dec (frame_ptr (nth (i - 1) (cg_frames s) None)) 0) as [Hpz | Hpz];
[pose proof (MK true Hpz) as HS | pose proof (MK false Hpz) as HS]; clear MK.
- br_tree ltac:(idtac; let HS := get_HS in let HJ := get_HJ in jrun_to LAWS ubs0tbl_ok HS HJ FL_F2; [apply WR; [exact HU2 | exact HU11] |]; kstep3 KSTEP HU2 HU11)
ltac:(idtac; let HS := get_HS in let HJ := get_HJ in
lazymatch goal with K : forall a, _ -> _ -> _ -> mbyte ubs0segs _ a = mbyte ubs0segs _ a |- _ =>
eapply (GO _ _ _ true false _ HS);
[ reflexivity | reflexivity
| do 2 eexists; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [vm_compute; reflexivity | cbn [r_chunks]; repeat (first [left; reflexivity | right])]
| exact Hpz
| first [ intros _; apply land3_and_m4 | intros _; apply land3_and_keep; apply land3_and_m4 | intros Hx; discriminate Hx ]
| vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity
| first [ exact I
| generalize (proj1 (proj2 (st_ok_facts_ok ubs0segs _ _ _ HS))); cbn [ss_facts f_conds conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b]; intros HC;
first [apply HAt; tauto | apply HAf; tauto] ]
| generalize (proj1 (proj2 (st_ok_facts_ok ubs0segs _ _ _ HS))); cbn [ss_facts f_conds conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b]; intros HC;
first [apply HSt; tauto | apply HSf; tauto]
| cbv beta iota delta [orb]; first [exact UEa | exact UEb | exact UEc | exact UEd]
| exact HJ | exact K ] end)
4%nat.
- br_tree ltac:(idtac; let HS := get_HS in let HJ := get_HJ in jrun_to LAWS ubs0tbl_ok HS HJ FL_F2; [apply WR; [exact HU2 | exact HU11] |]; kstep3 KSTEP HU2 HU11)
ltac:(idtac; let HS := get_HS in let HJ := get_HJ in
lazymatch goal with K : forall a, _ -> _ -> _ -> mbyte ubs0segs _ a = mbyte ubs0segs _ a |- _ =>
eapply (GO _ _ _ false _ _ HS);
[ reflexivity | reflexivity
| do 2 eexists; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [vm_compute; reflexivity | cbn [r_chunks]; repeat (first [left; reflexivity | right])]
| exact Hpz
| first [ intros _; apply land3_and_m4 | intros _; apply land3_and_keep; apply land3_and_m4 | intros Hx; discriminate Hx ]
| vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity
| first [ exact I
| generalize (proj1 (proj2 (st_ok_facts_ok ubs0segs _ _ _ HS))); cbn [ss_facts f_conds conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b]; intros HC;
first [apply HAt; tauto | apply HAf; tauto] ]
| generalize (proj1 (proj2 (st_ok_facts_ok ubs0segs _ _ _ HS))); cbn [ss_facts f_conds conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b]; intros HC;
first [apply HSt; tauto | apply HSf; tauto]
| cbv beta iota delta [orb]; first [exact UEa | exact UEb | exact UEc | exact UEd]
| exact HJ | exact K ] end)
4%nat. }
cbv beta. intros c' (L' & A' & regs' & mem' & md' & r & rwcur' & Hc' & HJ' & HRP & Hid' & G10' & Hr & Hat' & Hwf' & HB' & Hbytes & HRq').
exists L', A', regs', mem', md', r, rwcur'. split; [exact Hc'|].
split.
{ eapply (journal_fp_weaken API); [| exact HJ']. intros a Hin. subst FPw. apply (proj1 (inFP_app _ _ _)) in Hin as [Hin|Hin].
- destruct (HFPin a Hin) as [X|X]; unfold cgif_fp; apply (proj2 (inFP_cons _ _ _ _)); right; apply (proj2 (inFP_blocks_fp _ _));
[exists (cg_raw s), RAW_SIZE; split; [unfold cgif_blocks; right; left; reflexivity | clear - X HRWv; lia]
| exists (fr_ptr f), FRAME_SIZE; split; [unfold cgif_blocks; apply (frame_blocks_in_cgif g s N f); [exact Hfin | left; reflexivity] | clear - X HFRv; lia]].
- unfold cgif_fp. destruct Hin as (rr & [<- | [<- | []]] & Har); [exists sink_token; split; [left; reflexivity | exact Har]|].
apply (proj2 (inFP_cons _ _ _ _)). right. apply (proj2 (inFP_blocks_fp _ _)). exists (cg_file s), FILE_BLOCK. split; [unfold cgif_blocks; right; right; left; reflexivity | cbn [fst snd] in Har; exact Har]. }
split; [exact HRP|]. split; [exact Hid'|]. split; [exact G10'|]. split; [exact Hr|].
split; [exact Hat'|]. split; [exact Hwf'|]. split; [| split; [exact Hbytes | split; [exact HRq'|]]].
{ eapply Permutation_trans; [exact HB'|]. subst rest. apply Permutation_sym. apply cgif_blocks0_perm. }
intros a n k Hin Hnf Hk Hnr Hnfr.
assert (Hin' : In (a, n) (blocks L' A')).
{ apply (Permutation_in _ (Permutation_sym HB')). apply (Permutation_in _ HB). exact Hin. }
apply (journal_blocks_kept _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' a n k Hin Hin' Hk).
intros Hfp. subst FPw. apply (proj1 (inFP_app _ _ _)) in Hfp as [Hfp|Hfp].
- destruct (HFPin _ Hfp) as [X|X].
+ destruct (Z.eq_dec a (cg_raw s)) as [-> | Hne]; [apply Hnr; split; [reflexivity | clear - X; lia]|].
pose proof (heap_sep_in2 _ _ LAWS L A mem md (a, n) (cg_raw s, RAW_SIZE) HH Hin Hrawin ltac:(intros Eq0; injection Eq0 as E1 E2; exact (Hne E1))) as Y. cbn [fst snd] in Y. clear - X Y Hk HRWv. lia.
+ destruct (Z.eq_dec a (fr_ptr f)) as [-> | Hne]; [apply Hnfr; split; [reflexivity | clear - X; lia]|].
pose proof (heap_sep_in2 _ _ LAWS L A mem md (a, n) (fr_ptr f, FRAME_SIZE) HH Hin Hfblk ltac:(intros Eq0; injection Eq0 as E1 E2; exact (Hne E1))) as Y. cbn [fst snd] in Y. clear - X Y Hk HFRv. lia.
- destruct Hfp as (rr & [<- | [<- | []]] & Har); [unfold sink_token in Har; cbn [fst snd] in Har; destruct (blocks_range _ _ LAWS L A mem md a n HH Hin) as [R0 R1]; clear - Har R0 Hk; lia|].
cbn [fst snd] in Har. pose proof (heap_sep_in2 _ _ LAWS L A mem md (a, n) (cg_file s, FILE_BLOCK) HH Hin Hfilein Hnf) as Y. cbn [fst snd] in Y. clear - Har Y Hk. lia.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
