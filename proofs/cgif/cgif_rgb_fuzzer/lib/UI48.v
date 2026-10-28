(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i UI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g UI3h UI3d
UI4v UI46 UI4g.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_LDR (T : Z) : sstate :=
mkSS PC_RS (sr_set sr_atoms 10%bv (SLit T)) [] None (mkFacts [] [] []).
Section b.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation SP := (sp regs0).
Local Notation AT_RS := (at_RS API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_LD := (at_LD API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Section c.
Variables (i ha : Z) (Lc : layout) (Ac : astate) (mdc : Model) (pnew fimg : Z) (imgl : list Z) (C : cht).
Hypothesis KLD : forall regs1 memc, AT_LD regs1 Lc Ac memc mdc i ha pnew fimg imgl C ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_LD) memc (seg_rom ubs2segs)) mdc) POST.
Theorem RS_stretch : forall regs1 memc, AT_RS regs1 Lc Ac memc mdc i ha pnew fimg imgl C ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_RS) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 memc HAT. pose proof HAT as (HINV & HREGS & Hfmt & Hi & Hha & G10 & G9 & G20 & G8 & G21 & HTlt & S72 & HMEM).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof HMEM as (Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & Hfc & Hobj & Hcg & Himg & Hcht & EhS & EuS & ETS & Hz & Hpn & Hfi & HB).
pose proof Hcht as (Hobjc & _ & Hinv & HT & Hch & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
set (T := ch_T C) in *.
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HS : st_ok ubs2segs E (ss_LDR T) (mkst regs1 (Z_to_bv 64 PC_RS) memc (seg_rom ubs2segs))).
{ unfold ss_LDR. subst E. apply entry_st_ok_gen.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G10; reflexivity].
- vm_compute. reflexivity.
- constructor.
- exact I.
- exact I. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_RS) memc (seg_rom ubs2segs))) in HJ. clearbody E.
assert (ARR : forall ss ms' T', st_ok ubs2segs E ss ms' -> ss_resv ss = None -> ss_pc ss = PC_LD -> ms_mem ms' = memc ->
T' = getNextPrimePower2 T -> sr_get (ss_regs ss) 19 = SLit T' ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 9; 20; 8; 21]%bv = true ->
SR ubs2segs (mkCfg ms' mdc) POST).
{ intros ss ms' T' HS' Hrv Hpc Hm ET' Q19 QK.
pose proof (regs_kept_of_st_ok ubs2segs E ss ms' regs1 [] _ HS' EA0 QK) as GK.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc, Hm. apply (KLD (ms_regs ms') memc). unfold at_LD.
split; [exact HINV|].
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|].
split; [rewrite (GK 9%bv ltac:(cbv; auto 20)); exact G9|].
split; [rewrite (GK 20%bv ltac:(cbv; auto 20)); exact G20|].
split; [rewrite (GK 8%bv ltac:(cbv; auto 20)); exact G8|].
split; [rewrite (GK 21%bv ltac:(cbv; auto 20)); exact G21|].
split; [exact HTlt|]. split; [exact S72|]. split; [exact HMEM|].
rewrite (st_ok_reg _ _ _ _ 19%bv HS'), Q19; cbn [sv_denot]; subst T; rewrite <- ET'; reflexivity. }
assert (HT5 : T = 524309 \/ T = 1048583 \/ T = 2097169 \/ T = 4194319 \/ T = 8388617).
{ pose proof Hch as Hch0. cbv [ts_chain In] in Hch0. unfold MAX_TABLE_SIZE in HTlt. clear - Hch0 HTlt. lia. }
destruct HT5 as [ET | [ET | [ET | [ET | ET]]]]; rewrite ET in HS.
all: jrun_to LAWS ubs2tbl_ok HS HJ PC_LD; [apply wr_ok_nil |].
all: assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF)).
all: apply (ARR _ _ (getNextPrimePower2 T) HS eq_refl eq_refl Em eq_refl); [rewrite ET; vm_compute; reflexivity | vm_compute; reflexivity].
Qed.
End c.
End b.
End a.
