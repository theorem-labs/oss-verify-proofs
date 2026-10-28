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
UI4v UI46 UI43 UI44 UI45.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Theorem ubs2_rgbadd_HB : forall i,
seg_HB API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i.
Proof.
intros i KHL1 KHD KRS regs1 Lc Ac memc mdc ha pnew fimg imgl C HAT. unfold cfg_at.
set (PP := rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
assert (KHL' : forall regs mem ha' C',
at_HL API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest regs Lc Ac mem mdc (i + 1) ha' pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 PC_HL) mem (seg_rom ubs2segs)) mdc) PP).
{ intros regs mem ha' C' HA. exact (KHL1 regs Lc Ac mem mdc ha' pnew fimg imgl C' HA). }
assert (KHD' : forall regs mem ha' C',
at_HD API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest regs Lc Ac mem mdc ha' pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 PC_HD) mem (seg_rom ubs2segs)) mdc) PP).
{ intros regs mem ha' C' HA. exact (KHD regs Lc Ac mem mdc ha' pnew fimg imgl C' HA). }
pose proof (INC_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i Lc Ac mdc pnew fimg imgl KHL' KHD') as KINC.
assert (KRS' : forall ha' regs mem C',
at_RS API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest regs Lc Ac mem mdc i ha' pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 PC_RS) mem (seg_rom ubs2segs)) mdc) PP).
{ intros ha' regs mem C' HA. exact (KRS regs Lc Ac mem mdc ha' pnew fimg imgl C' HA). }
pose proof (fun ha' => RT_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha' Lc Ac mdc pnew fimg imgl (KRS' ha') KINC) as KRT.
pose proof (fun ha' C0 => INS_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha' Lc Ac mdc pnew fimg imgl C0 (KRT ha')) as KINS.
pose proof (fun ha' => PX_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha' Lc Ac mdc pnew fimg imgl C (KRT ha') (KINS ha' C)) as KPX.
pose proof (fun ha' => L_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha' Lc Ac mdc pnew fimg imgl C (KPX ha')) as KL.
exact (HL_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i Lc Ac mdc pnew fimg imgl C KINC
(fun regs mem ha' => KPX ha' 0 regs mem) (fun regs mem ha' => KL ha' regs mem) regs1 memc ha HAT).
Qed.
End b.
End a.
