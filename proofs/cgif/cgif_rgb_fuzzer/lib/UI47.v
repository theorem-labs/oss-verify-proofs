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
UI4v UI46 UI45 UI4g
UI48 UI49 UI4a UI4b UI4c UI4d UI4e UI4f.
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
Hypothesis REALLOC : realloc_realizes ubs2_msyms MR.
Hypothesis FCHT : forall fx', free_cht_spec (fx:=fx') API.
Hypothesis COLHASH : forall fx', col_hash_spec (fx:=fx') API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation CFG pc regs mem mdc := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs2segs)) mdc).
Theorem ubs2_rgbadd_HR : forall i,
seg_HR API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i.
Proof.
intros i KHL1 KHD KXB regs1 Lc1 Ac1 memc1 mdc1 ha pnew fimg imgl C HAT. unfold cfg_at.
assert (KINC : forall C' regs Lc Ac mem mdc,
at_INC API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest regs Lc Ac mem mdc i ha pnew fimg imgl C' ->
SR ubs2segs (CFG PC_INC regs mem mdc) POST).
{ intros C' regs Lc Ac mem mdc HA.
refine (INC_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i Lc Ac mdc pnew fimg imgl _ _ regs mem ha C' HA).
- intros regs' mem' ha' C'' HA'. exact (KHL1 regs' Lc Ac mem' mdc ha' pnew fimg imgl C'' HA').
- intros regs' mem' ha' C'' HA'. exact (KHD regs' Lc Ac mem' mdc ha' pnew fimg imgl C'' HA'). }
set (T' := getNextPrimePower2 (ch_T C)).
assert (KPOST : forall p1 x1 h1 u1 f1 K regs Lc Ac mem mdc,
at_POST API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest regs Lc Ac mem mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K ->
SR ubs2segs (CFG PC_POST regs mem mdc) POST).
{ intros p1 x1 h1 u1 f1 K.
apply (POST_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K).
apply (P1_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K).
apply (P2_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K).
apply (P3_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K).
intros regs Lc Ac mem mdc HA. exact (KINC _ regs Lc Ac mem mdc HA). }
assert (KREH : forall p1 x1 h1 u1 f1 Lc Ac mdc n j, ch_T C - j <= Z.of_nat n -> forall K regs mem,
at_REH API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest regs Lc Ac mem mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K j ->
SR ubs2segs (CFG PC_REH regs mem mdc) POST).
{ intros p1 x1 h1 u1 f1 Lc Ac mdc n. induction n as [|n IHn]; intros j Hn K regs mem HA.
- exfalso. destruct HA as (_ & _ & _ & _ & Hj & _). clear -Hn Hj. simpl in Hn. lia.
- refine (REH_round API IMG COLHASH L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha Lc Ac mdc pnew fimg imgl C T' p1 x1 h1 u1 f1 K j _ _ _ regs mem HA).
+ refine (RB_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha Lc Ac mdc pnew fimg imgl C T' p1 x1 h1 u1 f1 K j _ _).
* intros regs' mem' K' Hlt HA'. refine (IHn (j + 1) _ K' regs' mem' HA'). clear -Hn; rewrite Nat2Z.inj_succ in Hn; lia.
* intros regs' mem' K' HA'. exact (KPOST p1 x1 h1 u1 f1 K' regs' Lc Ac mem' mdc HA').
+ intros regs' mem' Hlt HA'. refine (IHn (j + 1) _ K regs' mem' HA'). clear -Hn; rewrite Nat2Z.inj_succ in Hn; lia.
+ intros regs' mem' K' HA'. exact (KPOST p1 x1 h1 u1 f1 K' regs' Lc Ac mem' mdc HA'). }
assert (KC0 : forall regs Lc Ac mem mdc p1 x1 h1 u1 f1,
at_C0 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest regs Lc Ac mem mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (CFG PC_C0 regs mem mdc) POST).
{ apply (C0_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T').
apply (MS_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T').
intros regs Lc Ac mem mdc p1 x1 h1 u1 f1 K j HA.
pose proof HA as (_ & _ & _ & _ & Hj & _).
refine (KREH p1 x1 h1 u1 f1 Lc Ac mdc (Z.to_nat (ch_T C - j)) j _ K regs mem HA). clear -Hj; rewrite Z2Nat.id; lia. }
assert (KFAIL : forall regs Lc Ac mem mdc p1 x1 h1 u1 f1,
at_FAIL API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest regs Lc Ac mem mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (CFG PC_FAIL regs mem mdc) POST).
{ apply (FAIL_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T').
apply (FS_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T').
apply (F1_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T').
apply (F2_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T').
apply (F3_stretch API IMG FCHT L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T').
intros regs Lc Ac mem mdc HA. exact (KXB regs Lc Ac mem mdc pnew fimg HA). }
assert (KM5 := M5_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T' KFAIL KC0).
assert (KM4 := M4_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T' KM5).
assert (KM3 := M3_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T' KM4).
assert (KR2 := R2_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C T' KM3).
assert (KR1 := R1_stretch API IMG REALLOC L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C KR2).
assert (KLD := LD_stretch API IMG REALLOC L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha pnew fimg imgl C KR1).
exact (RS_stretch API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest i ha Lc1 Ac1 mdc1 pnew fimg imgl C
(fun regs mem HA => KLD regs Lc1 Ac1 mem mdc1 HA) regs1 memc1 HAT).
Qed.
End b.
End a.
