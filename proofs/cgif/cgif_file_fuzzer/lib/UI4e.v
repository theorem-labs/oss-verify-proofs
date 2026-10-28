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
YI06 UI5b YI09 YI08 YI0r YI0o UI1w UI3p UI3t UI3u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z UI5d YI0j YI0k YI6c YI01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI3w UI4j UI3y UI4i UI4f UI4h UI42 UI41 UI4g UI4c UI3z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2w UI2v UI3x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma land2_cases : forall x, 0 <= x -> Z.land x 2 = 0 \/ Z.land x 2 = 2.
Proof using.
intros x Hx.
pose proof (Z_land_upper x 2 ltac:(lia)) as Hr.
assert (Hb : Z.testbit (Z.land x 2) 0 = false) by (rewrite Z.land_spec; cbn; apply Bool.andb_false_r).
destruct (Z.eq_dec (Z.land x 2) 1) as [E|NE]; [rewrite E in Hb; discriminate Hb | lia].
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Lemma wtok'_mono : forall STK sp0 FP FP' bl0 b,
(forall a, inFP FP a -> inFP FP' a) -> wtok' STK sp0 FP bl0 b -> wtok' STK sp0 FP' bl0 b.
Proof using.
intros STK sp0 FP FP' bl0 b HF HW blc i Hin Hi. specialize (HW blc i Hin Hi).
unfold wr_byte in *. destruct HW as [H | [[H1 H2] | H]]; [left; exact H | right; left; split; [apply HF; exact H1 | exact H2] | right; right; exact H].
Qed.
Theorem ubs0_cgif_raw_addframe_X : lzw_specX API -> rawadd_specX API.
Proof using FWRITE IMG.
intros LZW. unfold rawadd_specX.
intros L A regs mem md raw g cfp gvals gct rattr W H sgct loops rcur lct img fattr w h top left delay slct disp tidx Nimg rest f S IMGV LCTV b
HPRE Hid HfinR HSK0 Hroom Hsp47 G10 G11 Hcfpal Hcfplo Hcfphi HOC HOR Hsgct HOG Hwfn Hfile Hw Hh HnP HnP2 HB Hlct HIMG0 HIMGlen HRq HRM.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFBv : FILE_BLOCK = 1264) by reflexivity.
pose proof HPRE as (HH & Hra & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & Htp & Herr).
assert (HnP1 : 1 <= w * h) by nia.
destruct (heap_blocks_range _ _ LAWS L A mem md raw RAW_SIZE HH ltac:(eapply blocks_perm_in; [exact HB | left; reflexivity]) ltac:(lia)) as (Hr0 & Hr1 & Hr16).
destruct (heap_blocks_range _ _ LAWS L A mem md g CGIF_SIZE HH ltac:(eapply blocks_perm_in; [exact HB | right; left; reflexivity]) ltac:(lia)) as (Hg0 & Hg1 & Hg16).
destruct (heap_blocks_range _ _ LAWS L A mem md img Nimg HH ltac:(eapply blocks_perm_in; [exact HB | right; right; left; reflexivity]) ltac:(lia)) as (Hi0 & Hi1 & Hi16).
assert (Hfin : In (f, FILE_BLOCK) (blocks L A)) by (eapply blocks_perm_in; [exact HB | right; right; right; exact HfinR]).
destruct (heap_blocks_range _ _ LAWS L A mem md f FILE_BLOCK HH Hfin ltac:(lia)) as (Hf0 & Hf1 & Hf16).
pose proof (heap_sep_perm _ _ LAWS L A mem md (raw, RAW_SIZE) _ (g, CGIF_SIZE) HH HB ltac:(left; reflexivity)) as S1.
pose proof (heap_sep_perm _ _ LAWS L A mem md (raw, RAW_SIZE) _ (img, Nimg) HH HB ltac:(right; left; reflexivity)) as S2.
pose proof (heap_sep_perm _ _ LAWS L A mem md (raw, RAW_SIZE) _ (f, FILE_BLOCK) HH HB ltac:(right; right; exact HfinR)) as S4.
assert (HB' : Permutation (blocks L A) ((g, CGIF_SIZE) :: (raw, RAW_SIZE) :: (img, Nimg) :: rest)) by (eapply Permutation_trans; [exact HB | apply perm_swap]).
pose proof (heap_sep_perm _ _ LAWS L A mem md (g, CGIF_SIZE) _ (img, Nimg) HH HB' ltac:(right; left; reflexivity)) as S3.
cbn [fst snd] in S1, S2, S3, S4.
pose proof (bv_unsigned_in_range 64 (getr regs 3)) as Hgp. change (bv_modulus 64) with (2 ^ 64) in Hgp.
set (cx := mkRC (spZ regs - 144) raw cfp g lct img fattr w h top left delay slct disp tidx gct rattr W H sgct loops rcur gvals Nimg rest
(ms_tp ubs0_msyms) (bv_unsigned (getr regs 3))
(bv_unsigned (getr regs 25)) (bv_unsigned (getr regs 26)) (bv_unsigned (getr regs 27)) f).
assert (Hpre : rcx_pre cx).
{ unfold rcx_pre; cbn. unfold RAW_SIZE, CGIF_SIZE in *.
assert (Hspm : (spZ regs - 144) mod 16 = 0).
{ replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
repeat split; first [exact Hspm | exact Hcfpal | exact Hr16 | exact Hg16 | exact Hi16 | exact Hwfn | exact Hfile | exact HfinR | reflexivity | lia]. }
assert (HO : ra_origin cx regs).
{ unfold ra_origin; cbn. split; [lia|]. split; [exact Htp|]. split; [symmetry; apply Z_to_bv_bv_unsigned|]. split; [exact Hra|]. split; [lia|].
split; [symmetry; apply Z_to_bv_bv_unsigned|]. split; symmetry; apply Z_to_bv_bv_unsigned. }
assert (Hobjs : objs_at mem cx (c_rcur cx)) by (split; [exact HOC | split; [exact HOR | exact HOG]]).
assert (HBc : Permutation (blocks L A) (c_blocks cx)) by exact HB.
assert (HnPe : c_nP cx = w * h) by reflexivity.
assert (HFPI : forall a, inFP [(raw + 40, raw + 44)] a -> inFP ((raw + 40, raw + 44) :: sink_fp f) a /\ a < alloc_ceiling).
{ intros a (r & [<- | []] & Hr). cbn [fst snd] in Hr. split; [exists (raw + 40, raw + 44); split; [left; reflexivity | cbn; lia] | unfold RAW_SIZE in *; lia]. }
assert (HJbig : forall L' A' mem' md', journal ubs0_msyms MR RAWADD_STK (spZ regs) [(raw + 40, raw + 44)] L A mem md L' A' mem' md' ->
journal ubs0_msyms MR RAWADD_STK (spZ regs) ((raw + 40, raw + 44) :: sink_fp f) L A mem md L' A' mem' md').
{ intros L' A' mem' md' HJ'. eapply (journal_sub ubs0_msyms MR); [apply journal_init; exact HPRE | exact HJ' | lia | lia | exact HFPI]. }
assert (HSKk : forall L' A' mem' md', journal ubs0_msyms MR RAWADD_STK (spZ regs) [(raw + 40, raw + 44)] L A mem md L' A' mem' md' ->
sink_at ubs0_msyms mem' md' f S /\ In (f, FILE_BLOCK) (blocks L' A')).
{ intros L' A' mem' md' HJ'. eapply (sink_kept ubs0_msyms MR); [exact HJ' | | exact Hfin | | exact HSK0].
- intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
- intros a Ha (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold RAW_SIZE, FILE_BLOCK in *. lia. }
apply (SR_mono _ _ (fun c' => ra_postR API [(c_raw cx + 40, c_raw cx + 44)] (ra_exitX cx IMGV LCTV) (fun s => res_ok s (rawadd_rb b)) cx L A mem md regs c' \/
((c_rcur cx = 0 \/ c_rcur cx = 6) /\ c_slct cx <= 256 /\ ra_post4R API ((c_raw cx + 40, c_raw cx + 44) :: sink_fp (c_f cx)) (QT3 IMGV LCTV cx S) (fun s => res_ok s (rawadd_rb b)) cx L A mem md regs c'))).
2:{ pose proof (objs_fields_ok _ _ _ Hobjs) as (_ & _ & _ & _ & _ & _ & _ & _ & F8 & _).
intros c' [HP | (Hrc & Hsl & HP)].
- destruct HP as (L' & A' & regs' & mem' & md' & res & rcur' & -> & HJ' & HPr & Hid' & G10' & HOR' & HB2' & HQ & HRP).
destruct (HSKk _ _ _ _ HJ') as [HSK' _].
exists L', A', regs', mem', md', res, rcur'. split; [reflexivity|]. split; [exact (HJbig _ _ _ _ HJ')|]. split; [exact HPr|]. split; [exact Hid'|].
split; [exact G10'|]. split; [exact HOR'|]. split; [exact HB2'|]. split; [| exact HRP].
destruct HQ as (code & Hm & Hres & Hcur).
exists code, []. rewrite app_nil_r. split; [exact Hm|]. split; [exact Hres|]. split; [exact Hcur|]. split; [exact HSK' | cbn; lia].
- destruct HP as (L' & A' & regs' & mem' & md' & res & rcur' & -> & HJ' & HPr & Hid' & G10' & HOR' & HB2' & HQ & HRP).
exists L', A', regs', mem', md', res, rcur'. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HPr|]. split; [exact Hid'|].
split; [exact G10'|]. split; [exact HOR'|]. split; [exact HB2'|]. split; [| exact HRP].
destruct HQ as (-> & -> & raster & Hras & HSKf & HLR). exists 0, (ra_gce cx ++ ra_hdr cx ++ ra_lctb cx LCTV ++ [ra_iclen cx - 1] ++ raster).
split; [| split; [reflexivity | split; [reflexivity | split; [exact HSKf |
pose proof (ra_record_length cx LCTV raster) as RL; subst cx; cbn [c_slct c_nP c_w c_h] in RL, F8, HLR, Hsl; apply RL; [lia | exact HLR] ]]]].
change (YO07.raw_addframe _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (ra_model cx IMGV LCTV).
rewrite (ra_model_lzw cx IMGV LCTV Hrc Hsl), Hras. reflexivity. }
eapply SR_bind; [eapply (ra_entry_R API IMG IMGV LCTV cx); try eassumption|].
cbv beta. intros c1 [Hdone | (Hsl & Hrc & regs1 & mem1 & -> & HJ1 & HR1 & G19a & G23a & Hobjs1 & HFS1)]; [apply SR_ret; left; exact Hdone|].
assert (Hcx : rcx_ok cx) by (split; [exact Hpre | exact Hsl]).
eapply SR_bind; [eapply (ra_pow2 API IMG cx); try eassumption|].
cbv beta. intros c2 (regs2 & mem2 & p & -> & HJ2 & HR2 & G19b & G23b & G22b & G24b & Hpow & G11b & Hobjs2 & HFS2 & HFB37 & G12b).
assert (Hp08 : 0 <= p <= 8) by (destruct Hpow as [P0 P1]; destruct (Z.eq_dec slct 0) as [Z0|Z1]; [rewrite (P0 Z0); lia | pose proof (P1 Z1); lia]).
eapply SR_bind; [eapply (ra_neff API IMG cx); try eassumption; [intros Hnz; destruct Hpow as [_ P1]; pose proof (P1 Hnz); lia]|].
cbv beta. intros c3 (regs3 & mem3 & ne & -> & HJ3 & HR3 & G23c & G22c & G10c & G24c & G11c & Hne & Hobjs3 & HFS3 & Hnev & HFB37c & HFB46c).
eapply SR_bind; [eapply (ra_icl API IMG cx); try eassumption|].
cbv beta. intros c4 (regs4 & mem4 & icl & idl & -> & HJ4 & HR4 & G23d & G22d & G10d & G24d & G18d & G25d & Hicl & Hidl & G13d & G14d & Hobjs4 & HFS4 & Hiclv & Hidlv & HFBC4).
assert (LZWPART : SR ubs0segs (mkCfg (mkst regs4 (Z_to_bv 64 PC_C) mem4 (seg_rom ubs0segs)) md)
(fun c' => ra_postR API [(c_raw cx + 40, c_raw cx + 44)] (ra_exitX cx IMGV LCTV) (fun s => res_ok s (rawadd_rb b)) cx L A mem md regs c' \/ at_OK API IMGV cx L A mem md regs p b c')).
{ pose proof (objs_fields_ok _ _ _ Hobjs) as (_ & _ & F2 & _).
destruct (land2_cases fattr ltac:(cbn in F2; lia)) as [Hl0 | Hl2].
- eapply (ra_plain_R API IMG IMGV LCTV LZW cx); try eassumption; [apply Permutation_refl | rewrite G10d; subst cx; cbn [c_fattr]; rewrite Hl0; reflexivity].
- eapply SR_bind; [eapply (ra_il1_R API IMG cx); try eassumption; [apply Permutation_refl | rewrite G10d; subst cx; cbn [c_fattr]; rewrite Hl2; reflexivity]|].
cbv beta. intros c5 H5.
eapply SR_bind; [eapply (ra_il2 API IMG IMGV cx); try eassumption|].
cbv beta. intros c6 (L6 & A6 & regs6 & mem6 & md6 & pint & -> & HJ6 & Hid6 & HRq6 & HB6 & Hwt6 & Hpnz & HR6 & G23f & G24f & G22f & G18f & G25f & G19f & G10f & G12f & Hobjs6 & HFS6 & HPIX6 & HPIXlen6 & HFBC6).
eapply (ra_il3_R API IMG IMGV LCTV LZW cx); try eassumption. subst cx; cbn [c_fattr]. rewrite Hl2. lia. }
eapply SR_bind; [exact LZWPART|].
cbv beta. intros c7 [Hdone | (L7 & A7 & regs7 & mem7 & md7 & bb & Lbb & M & -> & HJ7 & Hid7 & HRB7 & HR7 & G23g & G24g & G22g & HB7 & Hwt7 & W32 & W40 & HM & Hobjs7 & HFS7 & HVOK & HM2 & HFBC7)];
[apply SR_ret; left; exact Hdone|].
destruct (HSKk _ _ _ _ HJ7) as [HSK7 Hfin7].
eapply SR_bind; [eapply (ra_t1 API IMG IMGV FWRITE cx); try eassumption; [exact (HJbig _ _ _ _ HJ7) | exact (wtok'_mono _ _ _ _ _ _ (fun a Ha => proj1 (HFPI a Ha)) Hwt7) | subst cx; cbn [c_nP c_w c_h]; lia]|].
cbv beta. intros c8 (L8 & A8 & regs8 & mem8 & md8 & bb8 & Lbb8 & M8 & -> & HJ8 & Hid8 & HRB8 & HR8 & G23h & G24h & G22h & HB8 & Hwt8 & W32h & W40h & HM8 & Hobjs8 & HFS8 & HVOK8 & HM28 & HFBC8 & HSK8 & G19h).
eapply SR_bind; [eapply (ra_t2 API IMG IMGV LCTV FWRITE cx); try eassumption; subst cx; cbn [c_nP c_w c_h c_slct c_lct c_rest c_f]; first [lia | exact Hlct]|].
cbv beta. intros c9 H9.
eapply SR_mono; [eapply (ra_t3_R API IMG IMGV LCTV FWRITE cx); try eassumption; subst cx; cbn [c_nP c_w c_h]; lia|].
cbv beta. intros c' H'. right. split; [exact Hrc | split; [exact Hsl | exact H']].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
