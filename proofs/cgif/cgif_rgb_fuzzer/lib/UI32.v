(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m
YI00 YI02 YI01 YI03 YI04 UI1e UI2m UI2r
UI2s UI37 UI2t UI36 UI33 UI35
UI2v UI2x UI34 UI30 UI2u.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma land2_cases : forall x, 0 <= x -> Z.land x 2 = 0 \/ Z.land x 2 = 2.
Proof.
intros x Hx.
pose proof (Z_land_upper x 2 ltac:(lia)) as Hr.
assert (Hb : Z.testbit (Z.land x 2) 0 = false) by (rewrite Z.land_spec; cbn; apply Bool.andb_false_r).
destruct (Z.eq_dec (Z.land x 2) 1) as [E|NE]; [rewrite E in Hb; discriminate Hb | lia].
Qed.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Theorem ubs2_cgif_raw_addframe : lzw_spec API -> rawadd_spec API.
Proof.
intros LZW. unfold rawadd_spec.
intros L A regs mem md raw g cfp gvals gct rattr W H sgct loops rcur lct img fattr w h top left delay slct disp tidx Nimg rest
HPRE Hid G10 G11 Hcfpal Hcfplo Hcfphi HOC HOR Hsgct HOG Hwfn Hfile Hw Hh HnP HnP2 HB Hlct.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof HPRE as (HH & Hra & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & Htp & Herr).
assert (HnP1 : 1 <= w * h) by nia.
destruct (heap_blocks_range _ _ LAWS L A mem md raw RAW_SIZE HH ltac:(eapply blocks_perm_in; [exact HB | left; reflexivity]) ltac:(lia)) as (Hr0 & Hr1 & Hr16).
destruct (heap_blocks_range _ _ LAWS L A mem md g CGIF_SIZE HH ltac:(eapply blocks_perm_in; [exact HB | right; left; reflexivity]) ltac:(lia)) as (Hg0 & Hg1 & Hg16).
destruct (heap_blocks_range _ _ LAWS L A mem md img Nimg HH ltac:(eapply blocks_perm_in; [exact HB | right; right; left; reflexivity]) ltac:(lia)) as (Hi0 & Hi1 & Hi16).
pose proof (heap_sep_perm _ _ LAWS L A mem md (raw, RAW_SIZE) _ (g, CGIF_SIZE) HH HB ltac:(left; reflexivity)) as S1.
pose proof (heap_sep_perm _ _ LAWS L A mem md (raw, RAW_SIZE) _ (img, Nimg) HH HB ltac:(right; left; reflexivity)) as S2.
assert (HB' : Permutation (blocks L A) ((g, CGIF_SIZE) :: (raw, RAW_SIZE) :: (img, Nimg) :: rest)) by (eapply Permutation_trans; [exact HB | apply perm_swap]).
pose proof (heap_sep_perm _ _ LAWS L A mem md (g, CGIF_SIZE) _ (img, Nimg) HH HB' ltac:(right; left; reflexivity)) as S3.
cbn [fst snd] in S1, S2, S3.
pose proof (bv_unsigned_in_range 64 (getr regs 3)) as Hgp. change (bv_modulus 64) with (2 ^ 64) in Hgp.
set (cx := mkRC (spZ regs - 144) raw cfp g lct img fattr w h top left delay slct disp tidx gct rattr W H sgct loops rcur gvals Nimg rest
(ms_tp ubs2_msyms) (bv_unsigned (getr regs 3))
(bv_unsigned (getr regs 25)) (bv_unsigned (getr regs 26)) (bv_unsigned (getr regs 27))).
assert (Hpre : rcx_pre cx).
{ unfold rcx_pre; cbn. unfold RAW_SIZE, CGIF_SIZE in *.
assert (Hspm : (spZ regs - 144) mod 16 = 0).
{ replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
repeat split; first [exact Hspm | exact Hcfpal | exact Hr16 | exact Hg16 | exact Hi16 | exact Hwfn | exact Hfile | reflexivity | lia]. }
assert (HO : ra_origin cx regs).
{ unfold ra_origin; cbn. split; [lia|]. split; [exact Htp|]. split; [symmetry; apply Z_to_bv_bv_unsigned|]. split; [exact Hra|]. split; [lia|].
split; [symmetry; apply Z_to_bv_bv_unsigned|]. split; symmetry; apply Z_to_bv_bv_unsigned. }
assert (Hobjs : objs_at mem cx (c_rcur cx)) by (split; [exact HOC | split; [exact HOR | exact HOG]]).
assert (HBc : Permutation (blocks L A) (c_blocks cx)) by exact HB.
apply (SR_mono _ _ (ra_post API cx L A mem md regs)); [| intros c' Hc'; exact Hc'].
eapply SR_bind; [eapply (ra_entry API IMG cx); try eassumption|].
cbv beta. intros c1 [Hdone | (Hsl & Hrc & regs1 & mem1 & -> & HJ1 & HR1 & G11' & G23 & Hobjs1 & HFS1)]; [apply SR_ret; exact Hdone|].
assert (Hcx : rcx_ok cx) by (split; [exact Hpre | exact Hsl]).
eapply SR_bind; [eapply (ra_pow2 API IMG cx); try eassumption|].
cbv beta. intros c2 (regs2 & mem2 & p & -> & HJ2 & HR2 & G11b & G23b & G10b & G27b & Hpow & G12b & Hobjs2 & HFS2).
assert (Hp08 : 0 <= p <= 8) by (destruct Hpow as [P0 P1]; destruct (Z.eq_dec slct 0) as [Z0|Z1]; [rewrite (P0 Z0); lia | pose proof (P1 Z1); lia]).
eapply SR_bind; [eapply (ra_neff API IMG cx); try eassumption|].
cbv beta. intros c3 (regs3 & mem3 & ne & -> & HJ3 & HR3 & G23c & G22c & G10c & G27c & G12c & Hne & Hobjs3 & HFS3).
eapply SR_bind; [eapply (ra_icl API IMG cx); try eassumption|].
cbv beta. intros c4 (regs4 & mem4 & icl & idl & -> & HJ4 & HR4 & G23d & G22d & G10d & G27d & G18d & G21d & Hicl & Hidl & G19d & G25d & Hobjs4 & HFS4).
assert (LZWPART : SR ubs2segs (mkCfg (mkst regs4 (Z_to_bv 64 PC_C) mem4 (seg_rom ubs2segs)) md)
(fun c' => ra_post API cx L A mem md regs c' \/ at_OK API cx L A mem md regs p c')).
{ pose proof (objs_fields_ok _ _ _ Hobjs) as (_ & _ & F2 & _).
destruct (land2_cases fattr ltac:(cbn in F2; lia)) as [Hl0 | Hl2].
- eapply (ra_plain API IMG LZW cx); try eassumption; [apply Permutation_refl | rewrite G10d; subst cx; cbn [c_fattr]; rewrite Hl0; reflexivity].
- eapply SR_bind; [eapply (ra_il1 API IMG cx); try eassumption; [apply Permutation_refl | rewrite G10d; subst cx; cbn [c_fattr]; rewrite Hl2; reflexivity]|].
cbv beta. intros c5 [Hdone | H5]; [apply SR_ret; left; exact Hdone|].
eapply SR_bind; [eapply (ra_il2 API IMG cx); try eassumption|].
cbv beta. intros c6 (L6 & A6 & regs6 & mem6 & md6 & pint & -> & HJ6 & Hid6 & HB6 & Hwt6 & Hpnz & HR6 & G23f & G22f & G18f & G20f & G19f & G25f & G27f & V16 & Hobjs6 & HFS6).
eapply (ra_il3 API IMG LZW cx); try eassumption. }
eapply SR_bind; [exact LZWPART|].
cbv beta. intros c7 [Hdone | (L7 & A7 & regs7 & mem7 & md7 & bb & Lbb & M & -> & HJ7 & Hid7 & HR7 & G23g & G22g & G27g & HB7 & Hwt7 & W32 & W40 & HM & Hobjs7 & HFS7)]; [apply SR_ret; exact Hdone|].
eapply SR_bind; [eapply (ra_t1 API IMG cx); try eassumption|].
cbv beta. intros c8 (L8 & A8 & regs8 & mem8 & md8 & bb8 & Lbb8 & M8 & -> & HJ8 & Hid8 & HR8 & G23h & G22h & G27h & HB8 & Hwt8 & W32h & W40h & HM8 & Hobjs8 & HFS8).
eapply SR_bind; [eapply (ra_t2 API IMG cx); try eassumption|].
cbv beta. intros c9 H9.
eapply (ra_t3 API IMG cx); try eassumption.
Qed.
End S.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
