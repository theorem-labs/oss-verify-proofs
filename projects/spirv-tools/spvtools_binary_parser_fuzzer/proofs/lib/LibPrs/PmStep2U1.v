(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module PmUpdU1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Inductive cix : Type := CM1 | CM2 | CM3 | CV1 | CV2 | CV3.
Scheme Equality for cix.

Definition chdr (i : cix) : Z * Z :=
  match i with CM1 => (O_M1, 40) | CM2 => (O_M2, 40) | CM3 => (O_M3, 40) | CV1 => (O_V1, 24) | CV2 => (O_V2, 24) | CV3 => (O_V3, 24) end.

Definition cblocks (i : cix) (c : pmc) : list (Z * Z) :=
  match i with
  | CM1 => umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c))
  | CM2 => umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
  | CM3 => umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))
  | CV1 => vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c))
  | CV2 => if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))]
  | CV3 => if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))]
  end.

Definition csame (i : cix) (c c' : pmc) : Prop :=
  match i with
  | CM1 => c_m1 c' = c_m1 c | CM2 => c_m2 c' = c_m2 c | CM3 => c_m3 c' = c_m3 c
  | CV1 => c_v1 c' = c_v1 c | CV2 => c_v2 c' = c_v2 c | CV3 => c_v3 c' = c_v3 c
  end.

Definition ALL : list cix := [CM1; CM2; CM3; CV1; CV2; CV3].

Section Upd.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.
Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
Hypothesis HLerr_img : forall a, errno_win L a -> in_ranges (ly_img L) a.
Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.
Context (w : pmw MI ST).

#[local] Notation PMX := (PmBaseU1.PMX MI ST).
#[local] Notation fprot := (PmBaseU1.fprot w).
#[local] Notation hi_unownedS := (hi_unowned MI HLimg_lo HLrw_img).
#[local] Notation fprot_factsS := (fprot_facts SEGS L MI ST HLimg_lo HLrw_img w).
#[local] Notation eff_dropS := (eff_drop SEGS L MI HLimg_lo HLrw_img).
#[local] Notation agree_via_effS := (agree_via_eff SEGS L MI).
#[local] Notation sx_inv_via_effS := (sx_inv_via_eff SEGS L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw).
#[local] Notation ro_clear_via_effS := (ro_clear_via_eff SEGS L MI HLimg_lo HLerr_rw).

Definition crep (i : cix) (A : AS MI) (M : mem) (c : pmc) : Prop :=
  match i with
  | CM1 => umapx MI 24 (nval24 SEGS) A M (w_p w + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c))
  | CM2 => umapx MI 32 (nval32 SEGS) A M (w_p w + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
  | CM3 => umapx MI 24 (nval24 SEGS) A M (w_p w + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))
  | CV1 => vec_opnd MI A M (w_p w + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c))
  | CV2 => vec32 MI A M (w_p w + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c))
  | CV3 => vec32 MI A M (w_p w + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c))
  end.

Definition cfoot (i : cix) (c : pmc) (a : Z) : Prop :=
  zwin (w_p w + fst (chdr i)) (w_p w + fst (chdr i) + snd (chdr i)) a
  \/ exists b, In b (cblocks i c) /\ fst b <= a < fst b + snd b.

Lemma cblk_flat : forall c, cblk c = flat_map (fun j => cblocks j c) ALL.
Proof using. intros c. unfold cblk, ALL. cbn [flat_map cblocks]. rewrite app_nil_r, <- ?app_assoc. reflexivity. Qed.

Lemma in_cblk : forall c b, In b (cblk c) <-> exists j, In b (cblocks j c).
Proof using.
  intros c b. rewrite cblk_flat, in_flat_map. split.
  - intros (j & _ & Hb). exists j. exact Hb.
  - intros (j & Hb). exists j. split; [destruct j; (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hb].
Qed.

Lemma csame_blocks : forall j c c', csame j c c' -> cblocks j c' = cblocks j c.
Proof using. intros j c c' H. destruct j; cbn in *; rewrite H; reflexivity. Qed.

Lemma pmx_crep : forall A M model c j, PMX w A M model c -> crep j A M c.
Proof using AC SEGS L MI ST w. intros A M model c j X. destruct j; cbn; [exact (x_m1 X) | exact (x_m2 X) | exact (x_m3 X) | exact (x_v1 X) | exact (x_v2 X) | exact (x_v3 X)]. Qed.

Lemma flat_nodup_ne : forall (f : cix -> list (Z * Z)) (l : list cix) i j b b',
  NoDup (map fst (flat_map f l)) -> List.NoDup l -> In i l -> In j l -> i <> j -> In b (f i) -> In b' (f j) -> fst b <> fst b'.
Proof using.
  intros f l. induction l as [|x l IH]; intros i j b b' ND NDl Hi Hj Hne Hb Hb'; [destruct Hi|].
  cbn in ND. rewrite map_app in ND. apply (proj1 (list_relations.list.NoDup_app _ _)) in ND. destruct ND as (N1 & NX & N2).
  inversion NDl as [|x' l' Hxl NDl']; subst.
  destruct Hi as [<-|Hi]; destruct Hj as [<-|Hj].
  - exfalso. exact (Hne eq_refl).
  - intros E. refine (NX (fst b) _ _).
    + apply list_elem_of_In. apply in_map_iff. exists b; auto.
    + rewrite E. apply list_elem_of_In. apply in_map_iff. exists b'. split; [reflexivity|]. apply in_flat_map. exists j; auto.
  - intros E. refine (NX (fst b') _ _).
    + apply list_elem_of_In. apply in_map_iff. exists b'; auto.
    + rewrite <- E. apply list_elem_of_In. apply in_map_iff. exists b. split; [reflexivity|]. apply in_flat_map. exists i; auto.
  - exact (IH i j b b' N2 NDl' Hi Hj Hne Hb Hb').
Qed.

Lemma ALL_nodup : List.NoDup ALL.
Proof using. unfold ALL. repeat (constructor; [cbn; intros HH; repeat (destruct HH as [HH|HH]; [discriminate HH|]); exact HH |]). constructor. Qed.

Lemma ALL_in : forall j, In j ALL.
Proof using. intros j; destruct j; unfold ALL; (first [solve [clear; cbn; tauto] | cbn; tauto]). Qed.

Lemma blk_junk : forall (A : AS MI) M model (X : list (Z * Z)) b a,
  ainv MI A M model -> Permutation (live MI A) (w_L0 w ++ X) -> In b X -> fst b <= a < fst b + snd b -> junkL MI w a.
Proof using AC SEGS L MI ST w.
  intros A M model X b a AI P Hb Ha. destruct b as [q k]. cbn in Ha.
  assert (Hl : In (q, k) (live MI A)) by (apply (Permutation_in _ (Permutation_sym P)); apply in_app_iff; right; exact Hb).
  destruct (ai_live_block MI A M model q k AI Hl) as (_ & _ & Hq0 & Hqc & Hpay). destruct (Hpay a ltac:(lia)) as (_ & Hni & _).
  split; [lia|]. split; [exact Hni|]. intros q' k' Hq' Hin.
  assert (Hl' : In (q', k') (live MI A)) by (apply (Permutation_in _ (Permutation_sym P)); apply in_app_iff; left; exact Hq').
  pose proof (perm_nodup_fst _ _ P (ai_live_nodup MI A M model AI)) as ND.
  assert (Hne : q' <> q).
  { apply (nodup_app_ne (w_L0 w) X); [exact ND | apply in_map_iff; exists (q', k'); auto | apply in_map_iff; exists (q, k); auto]. }
  exact (live_payload_disjoint SEGS L MI A M model q k q' k' a AI Hl Hl' ltac:(intros E; apply Hne; symmetry; exact E) Ha Hin).
Qed.

Lemma cblk_nodup : forall (A : AS MI) M model c tr,
  ainv MI A M model -> Permutation (live MI A) (w_L0 w ++ cblk c ++ tr) -> NoDup (map fst (cblk c)).
Proof using AC SEGS L MI ST w.
  intros A M model c tr AI P. pose proof (perm_nodup_fst _ _ P (ai_live_nodup MI A M model AI)) as ND.
  rewrite !map_app in ND. apply (proj1 (list_relations.list.NoDup_app _ _)) in ND. destruct ND as (_ & _ & ND).
  apply (proj1 (list_relations.list.NoDup_app _ _)) in ND. destruct ND as (ND & _ & _). exact ND.
Qed.

Lemma cblocks_ne : forall (A : AS MI) M model c tr i j b b',
  ainv MI A M model -> Permutation (live MI A) (w_L0 w ++ cblk c ++ tr) -> i <> j ->
  In b (cblocks i c) -> In b' (cblocks j c) -> fst b <> fst b'.
Proof using AC SEGS L MI ST w.
  intros A M model c tr i j b b' AI P Hne Hb Hb'.
  pose proof (cblk_nodup A M model c tr AI P) as ND. rewrite cblk_flat in ND.
  exact (flat_nodup_ne _ ALL i j b b' ND ALL_nodup (ALL_in i) (ALL_in j) Hne Hb Hb').
Qed.

Lemma cblocks_cblk : forall j c b, In b (cblocks j c) -> In b (cblk c).
Proof using. intros j c b Hb. apply (proj2 (in_cblk c b)). exists j. exact Hb. Qed.

Lemma chdr_range : forall i, 96 <= fst (chdr i) /\ fst (chdr i) + snd (chdr i) <= PARSER_SIZE /\ 0 < snd (chdr i).
Proof using. intros i; destruct i; unfold chdr, O_M1, O_M2, O_M3, O_V1, O_V2, O_V3, PARSER_SIZE; cbn; lia. Qed.
Lemma chdr_disj : forall i j a, i <> j ->
  fst (chdr i) <= a < fst (chdr i) + snd (chdr i) -> ~ (fst (chdr j) <= a < fst (chdr j) + snd (chdr j)).
Proof using. intros i j a Hne; destruct i, j; try (exfalso; exact (Hne eq_refl)); unfold chdr, O_M1, O_M2, O_M3, O_V1, O_V2, O_V3; cbn; lia. Qed.

Lemma crep_frame : forall j (A A' : AS MI) M M' c,
  crep j A M c ->
  CRep.agree_on (fun a => zwin (w_p w + fst (chdr j)) (w_p w + fst (chdr j) + snd (chdr j)) a
                           \/ exists b, In b (cblocks j c) /\ fst b <= a < fst b + snd b) M M' ->
  (forall b, In b (cblocks j c) -> In b (live MI A')) ->
  crep j A' M' c.
Proof using AC SEGS L MI ST w.
  intros j A A' M M' c R AG HL. destruct j; cbn in *.
  - eapply (umapx_agree SEGS L MI 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia)); [exact R | |].
    + intros a Ha. apply AG. destruct (umap_foot_cases 24 _ _ _ _ a Ha) as [Ho|Hb]; [left; unfold zwin, O_M1 in *; lia | right; exact Hb].
    + intros p n Hb _. apply HL. exact Hb.
  - eapply (umapx_agree SEGS L MI 32 (Z * Z * Z)%type (nval32 SEGS) (nval32_agree SEGS) ltac:(lia)); [exact R | |].
    + intros a Ha. apply AG. destruct (umap_foot_cases 32 _ _ _ _ a Ha) as [Ho|Hb]; [left; unfold zwin, O_M2 in *; lia | right; exact Hb].
    + intros p n Hb _. apply HL. exact Hb.
  - eapply (umapx_agree SEGS L MI 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia)); [exact R | |].
    + intros a Ha. apply AG. destruct (umap_foot_cases 24 _ _ _ _ a Ha) as [Ho|Hb]; [left; unfold zwin, O_M3 in *; lia | right; exact Hb].
    + intros p n Hb _. apply HL. exact Hb.
  - eapply vec_opnd_relive; [eapply vec_opnd_frame; [exact R | eapply agree_on_weaken; [exact AG|]; intros a Ha; left; unfold vec_opnd_fp, zwin, O_V1 in *; cbn; lia] |].
    intros Hb Hin. apply HL. unfold vec_opnd_blocks. destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [lia | left; reflexivity].
  - eapply vec32_relive; [eapply vec32_frame; [exact R | eapply agree_on_weaken; [exact AG|]; intros a [Ha|[Hb Ha]]] |].
    + left. unfold zwin, O_V2 in *. cbn. lia.
    + right. exists (t3a (c_v2 c), 4 * t3c (c_v2 c)). split; [destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity] |].
      cbn. destruct R as (_ & _ & _ & Hlen & _). unfold zwin in Ha. lia.
    + intros Hb Hin. apply HL. destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity].
  - eapply vec32_relive; [eapply vec32_frame; [exact R | eapply agree_on_weaken; [exact AG|]; intros a [Ha|[Hb Ha]]] |].
    + left. unfold zwin, O_V3 in *. cbn. lia.
    + right. exists (t3a (c_v3 c), 4 * t3c (c_v3 c)). split; [destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity] |].
      cbn. destruct R as (_ & _ & _ & Hlen & _). unfold zwin in Ha. lia.
    + intros Hb Hin. apply HL. destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity].
Qed.

Definition junkA (A : AS MI) (a : Z) : Prop :=
  0 < a < alloc_ceiling /\ ~ in_ranges (ly_img L) a /\ forall q k, In (q, k) (live MI A) -> ~ (q <= a < q + k).

Lemma pmx_updJ : forall (i : cix) A M model c A' M' model' c' (S : Z) (F : Z -> Prop),
  PMX w A M model c ->
  ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
  eff MI A A' M M' (w_sp w - S, w_sp w) F -> 0 <= S <= w_STK w - PM_FRAME ->
  (forall a, F a -> cfoot i c a \/ cfoot i c' a \/ zwin (w_sp w) (w_sp0 w - 104) a \/ junkA A a) ->
  (forall a, F a -> zwin (w_sp w) (w_sp0 w - 104) a -> M' (Z_to_bv 64 a) <> None) ->
  (forall j, j <> i -> csame j c c') ->
  c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c -> c_tr c' = c_tr c ->
  crep i A' M' c' ->
  Permutation (live MI A') (w_L0 w ++ c_blocks c') ->
  PMX w A' M' model' c'.
Proof using AC SEGS L MI ST HLimg_lo HLrw_img HLrelro_img HLerr_img HLrw_relro HLerr_rw w.
  intros i A M model c A' M' model' c' S F X AI' MS' FS' FDS' EF HS HF HFdef HSAME Ew Ei Ee Ef Et REP HPERM.
  pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
  destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw).
  pose proof (x_live X) as PL. rewrite c_blocks_split in PL.
  pose proof HPERM as PL'. rewrite c_blocks_split, Et in PL'.
  assert (HL0' : forall b, In b (w_L0 w) -> In b (live MI A')).
  { intros b Hb. apply (Permutation_in b (Permutation_sym HPERM)). apply in_app_iff. left. exact Hb. }
  assert (HI : forall x, alloc_ceiling <= x -> ~ in_ranges (ly_img L) x) by (intros x Hx Hi; pose proof (HLimg_lo _ Hi); lia).

  assert (BLK : forall b a, In b (cblk c) -> fst b <= a < fst b + snd b -> junkL MI w a /\ ~ owned MI A a /\ M (Z_to_bv 64 a) <> None).
  { intros b a Hb Ha. split; [eapply (blk_junk A M model (cblk c ++ c_tr c)); [exact AI | exact PL | apply in_app_iff; left; exact Hb | exact Ha] |].
    destruct b as [q k]. cbn in Ha. pose proof (cblk_live w _ X Hb) as Hl.
    destruct (ai_live_block MI A M model q k AI Hl) as (_ & _ & _ & _ & Hpay). destruct (Hpay a ltac:(lia)) as (Ho & _ & Hd). split; [exact Ho | exact Hd]. }
  assert (BLK' : forall b a, In b (cblk c') -> fst b <= a < fst b + snd b -> junkL MI w a).
  { intros b a Hb Ha. eapply (blk_junk A' M' model' (cblk c' ++ c_tr c)); [exact AI' | exact PL' | apply in_app_iff; left; exact Hb | exact Ha]. }

  assert (HKEEP : forall j b, j <> i -> In b (cblocks j c) -> In b (live MI A')).
  { intros j b Hj Hb. apply (Permutation_in b (Permutation_sym PL')). rewrite !in_app_iff. right; left.
    apply (cblocks_cblk j). rewrite (csame_blocks j c c' (HSAME j Hj)). exact Hb. }
  assert (HL0A : forall b, In b (w_L0 w) -> In b (live MI A)).
  { intros b Hb. apply (Permutation_in b (Permutation_sym (x_live X))). apply in_app_iff. left. exact Hb. }
  assert (JL : forall a, junkA A a -> junkL MI w a).
  { intros a (J1 & J2 & J3). split; [exact J1|]. split; [exact J2|]. intros q k Hqk. exact (J3 q k (HL0A _ Hqk)). }
  assert (JNK : forall a, junkA A a -> PmBaseU1.fprot w c a -> False).
  { intros a (J1 & J2 & J3) Ha. unfold PmBaseU1.fprot in Ha. destruct Ha as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]];
      unfold zwin, w_sp0, PM_FRAME, PARSER_SIZE in *; try lia.
    - destruct (Gw Hwz) as (_ & _ & _ & Wpl & _). destruct Wpl as [Whi|(q & k & Hqk & Hq1 & Hq2)]; [lia|].
      exact (J3 q k (HL0A _ Hqk) ltac:(lia)).
    - destruct b as [q k]. cbn in Hab. exact (J3 q k (cblk_live w _ X Hb) Hab). }
  assert (HFimg : forall a, F a -> ~ in_ranges (ly_img L) a).
  { intros a Ha. destruct (HF a Ha) as [[Hh|(b & Hb & Hab)]|[[Hh|(b & Hb & Hab)]|[Hz|Hj]]].
    - apply HI. unfold zwin, w_sp0, PM_FRAME in *. pose proof (chdr_range i). lia.
    - exact (proj1 (proj2 (proj1 (BLK b a (cblocks_cblk i c b Hb) Hab)))).
    - apply HI. unfold zwin, w_sp0, PM_FRAME in *. pose proof (chdr_range i). lia.
    - exact (proj1 (proj2 (BLK' b a (cblocks_cblk i c' b Hb) Hab))).
    - apply HI. unfold zwin, w_sp0, PM_FRAME in *. lia.
    - exact (proj1 (proj2 Hj)). }

  set (P := fun a => fprot c a /\ ~ cfoot i c a /\ ~ cfoot i c' a).
  assert (AG : CRep.agree_on P M M').
  { eapply agree_via_effS; [exact EF|]. intros a (Ha & Hn1 & Hn2).
    destruct (fprot_factsS A M model c a X Ha) as (Hr & Ho & Hd & Hni & Hhi & _).
    split; [exact Hr|]. split; [exact Ho|]. split.
    {
      unfold PmBaseU1.fprot in Ha. destruct Ha as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]].
      - apply (hi_unownedS _ AI'). unfold zwin, w_sp0, PM_FRAME in *. lia.
      - apply (hi_unownedS _ AI'). unfold w_sp0, PM_FRAME in *. lia.
      - apply (hi_unownedS _ AI'). unfold w_sp0, PM_FRAME in *. lia.
      - destruct (Gw Hwz) as (_ & _ & _ & Wpl & _). unfold zwin in Hwd. destruct Wpl as [Whi|(q & k & Hqk & Hq1 & Hq2)].
        + apply (hi_unownedS _ AI'). unfold w_sp0, PM_FRAME in *. lia.
        + destruct (ai_live_block MI A' M' model' q k AI' (HL0' _ Hqk)) as (_ & _ & _ & _ & Hpay'). exact (proj1 (Hpay' a ltac:(lia))).
      - apply (proj1 (in_cblk c b)) in Hb. destruct Hb as (j & Hb).
        destruct (cix_eq_dec j i) as [->|Hj]; [exfalso; apply Hn1; right; exists b; split; assumption|].
        destruct b as [q k]. cbn in Hab.
        destruct (ai_live_block MI A' M' model' q k AI' (HKEEP j _ Hj Hb)) as (_ & _ & _ & _ & Hpay'). exact (proj1 (Hpay' a ltac:(lia))). }
    split; [exact Hd|]. split.
    { intros Hf. destruct (HF a Hf) as [H1|[H2|[Hz|Hj]]]; [exact (Hn1 H1) | exact (Hn2 H2) | | exact (JNK a Hj Ha)].
      destruct Hhi as [Hhi|Hhi]; unfold zwin, w_sp0, PM_FRAME in *; [| lia].
      unfold PmBaseU1.fprot in Ha. destruct Ha as [Hs|[Hp|[Hc|[[Hwz Hwd]|(b & Hb & Hab)]]]]; unfold zwin, w_sp0, PM_FRAME, PARSER_SIZE in *; try lia.
      - destruct (Gw Hwz) as (_ & _ & _ & _ & Wdj). destruct (Wdj a Hwd) as [X1 _]. apply X1. unfold zwin. lia.
      - pose proof (proj1 (proj1 (BLK b a Hb Hab))). lia. }
    split.
    - unfold W_of. cbn. intros Hw'. destruct Hhi as [Hhi|Hhi]; [lia|]. unfold w_sp0, PM_FRAME in *. lia.
    - intros He. exact (Hni (HLerr_img _ He)). }
  assert (AGs : forall Q, (forall a, Q a -> P a) -> CRep.agree_on Q M M').
  { intros Q HQ a Ha. apply AG. apply HQ. exact Ha. }

  assert (NCF : forall cc a, w_p w <= a < w_p w + 96 \/ w_cons w + 32 <= a < w_cons w + 40 \/ zwin (w_sp0 w - 104) (w_sp0 w) a
                        \/ (w_words w <> 0 /\ zwin (w_words w) (w_words w + 4 * w_n w) a) ->
                        (cc = c \/ cc = c') -> ~ cfoot i cc a).
  { intros cc a Ha Hcc [Hh|(b & Hb & Hab)].
    - pose proof (chdr_range i). unfold zwin, w_sp0, PM_FRAME, PARSER_SIZE, apart in *.
      destruct Ha as [Ha|[Ha|[Ha|[Hwz Hwd]]]]; try lia.
      destruct (Gw Hwz) as (_ & _ & _ & _ & Wdj). destruct (Wdj a Hwd) as [_ X2]. apply X2. lia.
    - assert (Hj : junkL MI w a) by (destruct Hcc as [-> | ->]; [exact (proj1 (BLK b a (cblocks_cblk i c b Hb) Hab)) | exact (BLK' b a (cblocks_cblk i c' b Hb) Hab)]).
      destruct Hj as (Hlo & _ & HL0). unfold zwin, w_sp0, PM_FRAME in *.
      destruct Ha as [Ha|[Ha|[Ha|[Hwz Hwd]]]]; try lia.
      destruct (Gw Hwz) as (_ & _ & _ & Wpl & _). destruct Wpl as [Whi|(q & k & Hqk & Hq1 & Hq2)]; [lia|].
      exact (HL0 q k Hqk ltac:(lia)). }
  assert (FLD : forall a k v, CRep.fld SEGS M a k v -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                (forall x, a <= x < a + Z.of_nat k -> w_p w <= x < w_p w + 96 \/ w_cons w + 32 <= x < w_cons w + 40) -> CRep.fld SEGS M' a k v).
  { intros a k v Hf Ha Hk HQ. eapply fld_agree; [exact Ha | exact Hk | exact Hf |]. apply AGs. intros x Hx. unfold zwin in Hx.
    destruct (HQ x Hx) as [H1|H2].
    - split; [right; left; unfold PARSER_SIZE; lia|]. split; apply NCF; tauto.
    - split; [right; right; left; lia|]. split; apply NCF; tauto. }

  assert (CONT : forall j, crep j A' M' c').
  { intros j. destruct (cix_eq_dec j i) as [->|Hj]; [exact REP|].
    assert (Rj : crep j A M c').
    { pose proof (pmx_crep A M model c j X) as R0. destruct j; cbn in R0 |- *; rewrite (HSAME _ Hj); exact R0. }
    pose proof (csame_blocks j c c' (HSAME j Hj)) as EB.
    eapply (crep_frame j A A' M M' c' Rj).
    - apply AGs. intros a Ha. pose proof (chdr_range j) as CRj. pose proof (chdr_range i) as CRi.
      assert (HinC : forall b, In b (cblocks j c') -> In b (cblk c)) by (intros b Hb; rewrite EB in Hb; exact (cblocks_cblk j c b Hb)).
      split; [| split].
      + destruct Ha as [Hh|(b & Hb & Hab)]; [right; left; unfold zwin, PARSER_SIZE in *; lia | right; right; right; right; exists b; split; [exact (HinC b Hb) | exact Hab]].
      + intros [Hh'|(b' & Hb' & Hab')]; destruct Ha as [Hh|(b & Hb & Hab)].
        * exact (chdr_disj j i (a - w_p w) Hj ltac:(unfold zwin in Hh; lia) ltac:(unfold zwin in Hh'; lia)).
        * pose proof (proj1 (proj1 (BLK b a (HinC b Hb) Hab))). unfold zwin, w_sp0, PM_FRAME in *. lia.
        * pose proof (proj1 (proj1 (BLK b' a (cblocks_cblk i c b' Hb') Hab'))). unfold zwin, w_sp0, PM_FRAME in *. lia.
        * rewrite EB in Hb. destruct b as [q k], b' as [q' k']. cbn in Hab, Hab'.
          refine (live_payload_disjoint SEGS L MI A M model q k q' k' a AI _ _ _ Hab Hab');
            [exact (cblk_live w _ X (cblocks_cblk j c _ Hb)) | exact (cblk_live w _ X (cblocks_cblk i c _ Hb')) |].
          exact (cblocks_ne A M model c (c_tr c) j i (q, k) (q', k') AI PL ltac:(exact Hj) Hb Hb').
      + intros [Hh'|(b' & Hb' & Hab')]; destruct Ha as [Hh|(b & Hb & Hab)].
        * exact (chdr_disj j i (a - w_p w) Hj ltac:(unfold zwin in Hh; lia) ltac:(unfold zwin in Hh'; lia)).
        * pose proof (proj1 (proj1 (BLK b a (HinC b Hb) Hab))). unfold zwin, w_sp0, PM_FRAME in *. lia.
        * pose proof (proj1 (BLK' b' a (cblocks_cblk i c' b' Hb') Hab')). unfold zwin, w_sp0, PM_FRAME in *. lia.
        * destruct b as [q k], b' as [q' k']. cbn in Hab, Hab'.
          refine (live_payload_disjoint SEGS L MI A' M' model' q k q' k' a AI' _ _ _ Hab Hab');
            [apply (HKEEP j _ Hj); rewrite <- EB; exact Hb
            | apply (Permutation_in _ (Permutation_sym PL')); rewrite !in_app_iff; right; left; exact (cblocks_cblk i c' _ Hb') |].
          exact (cblocks_ne A' M' model' c' (c_tr c) j i (q, k) (q', k') AI' PL' ltac:(exact Hj) Hb Hb').
    - intros b Hb. apply (HKEEP j b Hj). rewrite <- EB. exact Hb. }
  unfold w_sp0, PARSER_SIZE, PM_FRAME in *.
  constructor; rewrite ?Ew, ?Ei, ?Ee, ?Ef, ?Et.
  all: unfold w_sp0, PARSER_SIZE, PM_FRAME in *.
  - exact AI'.
  - exact MS'.
  - rewrite FS'. exact (x_fs X).
  - rewrite FDS'. exact (x_fds X).
  - eapply sx_inv_via_effS; [exact (x_sx X) | exact AI | exact EF | exact (x_own_sx X) | exact (x_err_sx X) | exact HFimg | cbn; lia].
  - exact (x_sxh X).
  - eapply ro_clear_via_effS; [exact (x_roc X) | exact AI | exact EF | exact HFimg | cbn; lia].
  - assert (EF2 : eff MI A A' M M' (w_sp w + 864 - w_STK w, w_sp w + 864) (PMF MI w)).
    { eapply (eff_dropS A A' M M' model' _ (PMF MI w) (fun a => F a /\ zwin (w_sp w) (w_sp w + 864 - 104) a)); [| exact AI' | |].
      - eapply eff_weaken; [eapply eff_widen; [exact EF | cbn; lia | cbn; lia] |].
        intros a Ha. destruct (HF a Ha) as [[Hh|(b & Hb & Hab)]|[[Hh|(b & Hb & Hab)]|[Hz|Hj]]].
        + left. left. pose proof (chdr_range i). unfold zwin, PARSER_SIZE in *. lia.
        + left. right. exact (proj1 (BLK b a (cblocks_cblk i c b Hb) Hab)).
        + left. left. pose proof (chdr_range i). unfold zwin, PARSER_SIZE in *. lia.
        + left. right. exact (BLK' b a (cblocks_cblk i c' b Hb) Hab).
        + right. split; [exact Ha | exact Hz].
        + left. right. exact (JL a Hj).
      - intros a [_ Hz]. unfold W_of, zwin in *. cbn. lia.
      - intros a [Ha Hz] _. apply (HFdef a Ha). unfold zwin in *. lia. }
    eapply eff_weaken.
    + eapply eff_trans; [exact (x_eff X) | exact EF2 |].
      intros a Ha. apply (hi_unownedS _ AI'). unfold W_of in Ha. cbn in Ha. lia.
    + intros a [Ha|Ha]; exact Ha.
  - intros a Ho'. destruct (ef_own _ _ _ _ _ _ _ _ _ EF a Ho') as [Ho|[[Hni _]|Hf]].
    + exact (x_own_sx X a Ho).
    + intros Hs. exact (Hni (HLrw_img _ (sx_region_rw ST _ Hs))).
    + intros Hs. exact (HFimg a Hf (HLrw_img _ (sx_region_rw ST _ Hs))).
  - exact (x_err_sx X).
  - exact (x_win_sx X).
  - exact (x_geo X).
  - intros k Hk. pose proof (x_wdef X k Hk) as D0. unfold w_sp0, PM_FRAME in D0.
    destruct (ef_def _ _ _ _ _ _ _ _ _ EF (w_sp w + 864 - w_STK w + k) ltac:(lia) D0) as [H|[H|[H|H]]].
    + exact H.
    + exfalso. apply (x_wown X (w_sp w + 864 - w_STK w + k)); [unfold zwin, w_sp0, PM_FRAME; lia | exact H].
    + destruct (HF _ H) as [[Hh|(b & Hb & Hab)]|[[Hh|(b & Hb & Hab)]|[Hz|Hj]]].
      * exfalso. pose proof (chdr_range i). unfold zwin in *. lia.
      * exfalso. pose proof (proj1 (proj1 (BLK b _ (cblocks_cblk i c b Hb) Hab))). lia.
      * exfalso. pose proof (chdr_range i). unfold zwin in *. lia.
      * exfalso. pose proof (proj1 (BLK' b _ (cblocks_cblk i c' b Hb) Hab)). lia.
      * apply (HFdef _ H). unfold zwin in *. lia.
      * exfalso. pose proof (proj1 Hj). lia.
    + exfalso. pose proof (HLimg_lo _ (HLerr_img _ H)). lia.
  - intros a Ha. apply (hi_unownedS _ AI'). unfold zwin, w_sp0, PM_FRAME in Ha. lia.
  - intros k Hk. pose proof (x_slots X k Hk) as SL.
    rewrite (rdn_agree_win SEGS M M'); [exact SL | unfold w_sp0, PM_FRAME; lia | cbn; unfold w_sp0, PM_FRAME; lia |].
    apply AGs. intros a Ha. unfold zwin, w_sp0, PM_FRAME in Ha. cbn in Ha.
    split; [left; unfold zwin, w_sp0, PM_FRAME; lia|]. split; apply NCF; unfold zwin, w_sp0, PM_FRAME; first [tauto | lia].
  -
    assert (Hhdr : mdef M' (w_p w + fst (chdr i)) (snd (chdr i))).
    { destruct i; cbn in REP |- *.
      - apply u_hdr in REP. apply h_def in REP. exact REP.
      - apply u_hdr in REP. apply h_def in REP. exact REP.
      - apply u_hdr in REP. apply h_def in REP. exact REP.
      - destruct REP as (_ & _ & HD & _). exact HD.
      - destruct REP as (_ & _ & HD & _). exact HD.
      - destruct REP as (_ & _ & HD & _). exact HD. }
    pose proof (chdr_range i) as CR. unfold PARSER_SIZE in CR.
    intros k Hk. destruct (Z.lt_ge_cases k (fst (chdr i))) as [Hlt|Hge]; [| destruct (Z.lt_ge_cases k (fst (chdr i) + snd (chdr i))) as [Hlt2|Hge2]].
    + rewrite (AG (w_p w + k)); [exact (x_pdef X k Hk)|].
      split; [right; left; unfold PARSER_SIZE; lia|]. split; (intros [Hh|(b & Hb & Hab)]; [unfold zwin in Hh; lia|]);
        [pose proof (proj1 (proj1 (BLK b _ (cblocks_cblk i c b Hb) Hab))) | pose proof (proj1 (BLK' b _ (cblocks_cblk i c' b Hb) Hab))]; lia.
    + pose proof (Hhdr (k - fst (chdr i)) ltac:(lia)) as D. replace (w_p w + fst (chdr i) + (k - fst (chdr i))) with (w_p w + k) in D by lia. exact D.
    + rewrite (AG (w_p w + k)); [exact (x_pdef X k Hk)|].
      split; [right; left; unfold PARSER_SIZE; lia|]. split; (intros [Hh|(b & Hb & Hab)]; [unfold zwin in Hh; lia|]);
        [pose proof (proj1 (proj1 (BLK b _ (cblocks_cblk i c b Hb) Hab))) | pose proof (proj1 (BLK' b _ (cblocks_cblk i c' b Hb) Hab))]; lia.
  - apply FLD; [exact (x_cons X) | lia | cbn; lia | intros x Hx; cbn in Hx; left; lia].
  - apply FLD; [exact (x_user X) | lia | cbn; lia | intros x Hx; cbn in Hx; left; lia].
  - apply FLD; [exact (x_hdrfn X) | lia | cbn; lia | intros x Hx; cbn in Hx; left; lia].
  - apply FLD; [exact (x_insfn X) | lia | cbn; lia | intros x Hx; cbn in Hx; left; lia].
  - apply FLD; [exact (x_hunk X) | lia | cbn; lia | intros x Hx; cbn in Hx; left; lia].
  - apply FLD; [exact (x_words X) | unfold O_WORDS; lia | unfold O_WORDS; cbn; lia | intros x Hx; unfold O_WORDS in Hx; cbn in Hx; left; lia].
  - apply FLD; [exact (x_n X) | unfold O_N; lia | unfold O_N; cbn; lia | intros x Hx; unfold O_N in Hx; cbn in Hx; left; lia].
  - apply FLD; [exact (x_diag X) | unfold O_DIAG; lia | unfold O_DIAG; cbn; lia | intros x Hx; unfold O_DIAG in Hx; cbn in Hx; left; lia].
  - apply FLD; [exact (x_widx X) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | intros x Hx; unfold O_WIDX in Hx; cbn in Hx; left; lia].
  - apply FLD; [exact (x_icount X) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | intros x Hx; unfold O_ICOUNT in Hx; cbn in Hx; left; lia].
  - apply FLD; [exact (x_endian X) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | intros x Hx; unfold O_ENDIAN in Hx; cbn in Hx; left; lia].
  - apply FLD; [exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | intros x Hx; unfold O_FLAGS in Hx; cbn in Hx; left; lia].
  - exact (x_scal X).
  - apply FLD; [exact (x_consf X) | lia | cbn; lia | intros x Hx; cbn in Hx; right; lia].
  - eapply mdef_agree; [exact (x_consd X)|]. apply AGs. intros a Ha. unfold zwin in Ha.
    split; [right; right; left; lia|]. split; (apply NCF; [right; left; lia | tauto]).
  - intros Hwz. eapply mdef_agree; [exact (x_wbuf X Hwz)|]. apply AGs. intros a Ha.
    split; [right; right; right; left; split; [exact Hwz | exact Ha]|]. split; (apply NCF; [right; right; right; split; [exact Hwz | exact Ha] | tauto]).
  - exact (CONT CM1). - exact (CONT CM2). - exact (CONT CM3). - exact (CONT CV1). - exact (CONT CV2). - exact (CONT CV3).
  - exact HPERM.
  - pose proof (x_caps X) as (C1 & C2 & C3). rewrite (ef_caps _ _ _ _ _ _ _ _ _ EF), (ef_bigcap _ _ _ _ _ _ _ _ _ EF). repeat split; assumption.
Qed.

Lemma pmx_upd : forall (i : cix) A M model c A' M' model' c' (S : Z) (F : Z -> Prop),
  PMX w A M model c ->
  ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
  eff MI A A' M M' (w_sp w - S, w_sp w) F -> 0 <= S <= w_STK w - PM_FRAME ->
  (forall a, F a -> cfoot i c a \/ cfoot i c' a \/ zwin (w_sp w) (w_sp0 w - 104) a) ->
  (forall a, F a -> zwin (w_sp w) (w_sp0 w - 104) a -> M' (Z_to_bv 64 a) <> None) ->
  (forall j, j <> i -> csame j c c') ->
  c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c -> c_tr c' = c_tr c ->
  crep i A' M' c' ->
  Permutation (live MI A') (w_L0 w ++ c_blocks c') ->
  PMX w A' M' model' c'.
Proof using AC SEGS L MI ST HLimg_lo HLrw_img HLrelro_img HLerr_img HLrw_relro HLerr_rw w.
  intros i A M model c A' M' model' c' S F X AI' MS' FS' FDS' EF HS HF HFdef HSAME Ew Ei Ee Ef Et REP HPERM.
  eapply (pmx_updJ i A M model c A' M' model' c' S F X AI' MS' FS' FDS' EF HS); try eassumption.
  intros a Ha. destruct (HF a Ha) as [H1|[H2|H3]]; tauto.
Qed.

Definition crest (i : cix) (c : pmc) : list (Z * Z) :=
  flat_map (fun j => if cix_eq_dec j i then [] else cblocks j c) ALL.

Lemma flat_skip : forall (f : cix -> list (Z * Z)) (l : list cix) i,
  ~ In i l -> flat_map (fun j => if cix_eq_dec j i then [] else f j) l = flat_map f l.
Proof using.
  intros f l i. induction l as [|y l IH]; intros Hn; [reflexivity|]. cbn.
  destruct (cix_eq_dec y i) as [->|Hy]; [exfalso; apply Hn; left; reflexivity|].
  rewrite IH; [reflexivity|]. intros H; apply Hn; right; exact H.
Qed.

Lemma flat_pull : forall (f : cix -> list (Z * Z)) (l : list cix) i,
  List.NoDup l -> In i l ->
  Permutation (flat_map f l) (f i ++ flat_map (fun j => if cix_eq_dec j i then [] else f j) l).
Proof using.
  intros f l i ND Hi. induction l as [|x l IH]; [destruct Hi|]. cbn. inversion ND as [|x' l' Hxl NDl]; subst.
  destruct (cix_eq_dec x i) as [->|Hne].
  - cbn. rewrite (flat_skip f l i Hxl). apply Permutation_refl.
  - destruct Hi as [E|Hi]; [exfalso; exact (Hne E)|].
    eapply Permutation_trans; [apply Permutation_app_head; exact (IH NDl Hi)|]. apply Permutation_app_swap_app.
Qed.

Lemma cblk_split : forall i c, Permutation (cblk c) (cblocks i c ++ crest i c).
Proof using. intros i c. rewrite cblk_flat. unfold crest. apply (flat_pull (fun j => cblocks j c) ALL i); [exact ALL_nodup | exact (ALL_in i)]. Qed.

Lemma crest_same : forall i c c', (forall j, j <> i -> csame j c c') -> crest i c' = crest i c.
Proof using.
  intros i c c' HS. unfold crest. generalize ALL. intros l. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite IH. f_equal.
  destruct (cix_eq_dec x i) as [->|Hne]; [reflexivity|]. exact (csame_blocks x c c' (HS x Hne)).
Qed.

Lemma live_split : forall A M model c (i : cix),
  PMX w A M model c -> Permutation (live MI A) (cblocks i c ++ (w_L0 w ++ crest i c ++ c_tr c)).
Proof using AC SEGS L MI ST w.
  intros A M model c i X. eapply Permutation_trans; [exact (x_live X)|]. rewrite c_blocks_split.
  eapply Permutation_trans. { apply Permutation_app_head. apply Permutation_app_tail. exact (cblk_split i c). }
  rewrite <- (app_assoc (cblocks i c)). apply Permutation_app_swap_app.
Qed.

Lemma live_join : forall (A' : AS MI) c c' (i : cix),
  (forall j, j <> i -> csame j c c') -> c_tr c' = c_tr c ->
  Permutation (live MI A') (cblocks i c' ++ (w_L0 w ++ crest i c ++ c_tr c)) ->
  Permutation (live MI A') (w_L0 w ++ c_blocks c').
Proof using AC SEGS L MI ST w.
  intros A' c c' i HS Et P. eapply Permutation_trans; [exact P|]. rewrite (c_blocks_split c'), Et, <- (crest_same i c c' HS).
  apply Permutation_sym.
  eapply Permutation_trans. { apply Permutation_app_head. apply Permutation_app_tail. exact (cblk_split i c'). }
  rewrite <- (app_assoc (cblocks i c')). apply Permutation_app_swap_app.
Qed.

Lemma vec_xfer : forall (A A' : AS MI) M M' model model' (b cap b' cap' k : Z) (R : list (Z * Z)),
  ainv MI A M model -> ainv MI A' M' model' -> 0 < k ->
  Permutation (live MI A) ((if b =? 0 then [] else [(b, k * cap)]) ++ R) ->
  (b <> 0 -> 0 < cap) ->
  (live MI A' = live MI A /\ b' = b /\ cap' = cap
   \/ 0 < cap' /\ lapply (live MI A) (LAdd b' (k * cap') :: del_if b) (live MI A')) ->
  (b' = 0 -> cap' = 0) ->
  Permutation (live MI A') ((if b' =? 0 then [] else [(b', k * cap')]) ++ R).
Proof using AC SEGS L MI.
  intros A A' M M' model model' b cap b' cap' k R AI AI' Hk P Hcap HX Hb'.
  pose proof (ai_live_nodup MI A M model AI) as ND. pose proof (ai_live_nodup MI A' M' model' AI') as ND'.
  destruct HX as [(E & -> & ->)|(Hc' & lv1 & AD & DL)]; [rewrite E; exact P|].
  destruct (Z.eqb_spec b' 0) as [E0|N0]; [pose proof (Hb' E0); lia|]. cbn.
  unfold del_if in DL. destruct (Z.eqb_spec b 0) as [Eb|Nb].
  - cbn in DL, P. subst lv1. destruct (live_add_perm b' (k * cap') R _ _ P AD) as [P' _]. exact P'.
  - cbn in DL. destruct DL as (lv2 & D & E). rewrite E in ND' |- *. cbn in P.
    destruct (live_add_perm b' (k * cap') ((b, k * cap) :: R) _ _ P AD) as [P1 Hnin].
    destruct AD as [Elv1 _].
    assert (N1 : NoDup (map fst lv1)).
    {
      rewrite Elv1. cbn. apply NoDup_cons_2; [| exact ND]. intros Hin. apply Hnin. apply list_elem_of_In in Hin.
      apply (Permutation_in b' (Permutation_map fst P)) in Hin. exact Hin. }
    apply (live_del_perm b (k * cap) ((b', k * cap') :: R) lv1 lv2); [| exact N1 | exact D | exact ND'].
    eapply Permutation_trans; [exact P1 | apply perm_swap].
Qed.
End Upd.
End PmUpdU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts ContStmts2 U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cu_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreU1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepU1.pmx_ds_room CL).
  #[local] Notation pm_tail_6733c := (PmStepU1.pm_tail_6733c CL).
  #[local] Notation cregs_kept := (PmStepU1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_chars := (PmStepU1.pm_put_chars CL).
  #[local] Notation pm_put_num := (PmStepU1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepU1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepU1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepU1.pm_put_int CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepU1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepU1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepU1.pm_binend CL).

  Definition set_v1 (c : pmc) (v : Z * Z * Z) : pmc :=
    {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
       c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := v; c_v2 := c_v2 c; c_v3 := c_v3 c; c_tr := c_tr c |}.
  Definition set_v2 (c : pmc) (v : Z * list Z * Z) : pmc :=
    {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
       c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := c_v1 c; c_v2 := v; c_v3 := c_v3 c; c_tr := c_tr c |}.
  Definition set_v3 (c : pmc) (v : Z * list Z * Z) : pmc :=
    {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
       c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := c_v1 c; c_v2 := c_v2 c; c_v3 := v; c_tr := c_tr c |}.

  #[local] Notation pmx_updS := (pmx_upd SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_errno_img ly_rw_not_relro ly_errno_rw).
  #[local] Notation live_splitS := (live_split SEGS Ly.L MI ST).
  #[local] Notation live_joinS := (live_join SEGS Ly.L MI ST).
  #[local] Notation vec_xferS := (vec_xfer SEGS Ly.L MI).

  Lemma pmx_upd_foot : forall (i : cix) (w : pmw MI ST) A M M' model c c' (W : Z -> Prop),
    PMX w A M model c -> stores_in W M M' ->
    (forall a, W a -> cfoot SEGS Ly.L MI ST w i c a) ->
    (forall j, j <> i -> csame j c c') ->
    c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c -> c_tr c' = c_tr c ->
    cblocks i c' = cblocks i c ->
    crep SEGS Ly.L MI ST w i A M' c' ->
    PMX w A M' model c'.
  Proof using AC MI ST.
    intros i w A M M' model c c' W X SI HW HS Ew Ei Ee Ef Et Eb REP.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (chdr_range i) as CR. unfold PARSER_SIZE in CR.
    assert (HWno : forall a, W a -> ~ owned MI A a).
    { intros a Ha. destruct (HW a Ha) as [Hh | (b & Hb & Hab)].
      - apply (hi_unowned MI ly_img_low ly_rw_img a AI). unfold zwin in Hh. lia.
      - destruct b as [q k]. cbn in Hab.
        assert (Hl : In (q, k) (live MI A)) by (eapply cblk_live; [exact X | apply (proj2 (in_cblk c (q, k))); exists i; exact Hb]).
        destruct (ai_live_block MI A M model q k AI Hl) as (_ & _ & _ & _ & Hall). exact (proj1 (Hall a Hab)). }
    assert (AI' : ainv MI A M' model).
    { eapply stores_in_ainv; [exact AI | exact SI | exact HWno]. }
    eapply (pmx_updS w i A M model c A M' model c' 0 W X AI' (x_ms X) eq_refl eq_refl);
      [ | unfold PM_FRAME; lia | intros a Ha; left; exact (HW a Ha)
      | intros a Ha Hz; exfalso; destruct (HW a Ha) as [Hh | ([q k] & Hb & Hab)];
          [unfold zwin, w_sp0, PM_FRAME in *; lia
          | cbn in Hab; assert (Hl : In (q, k) (live MI A)) by (eapply cblk_live; [exact X | apply (proj2 (in_cblk c (q, k))); exists i; exact Hb]);
            destruct (ai_live_block MI A M model q k AI Hl) as (_ & _ & _ & Hqc & _); unfold zwin, w_sp0, PM_FRAME in *; lia]
      | exact HS | exact Ew | exact Ei | exact Ee | exact Ef | exact Et | exact REP |].
    - apply eff_store; [| exact (proj2 SI)]. intros a Hf _. apply (proj1 SI). exact Hf.
    - eapply (live_joinS w A c c' i HS Et). rewrite Eb. exact (live_splitS w A M model c i X).
  Qed.

  Lemma pm_v2_push_fast : forall (w : pmw MI ST) A M model c (b cap : Z) (xs : list Z) (u : word),
    PMX w A M model c -> c_v2 c = (b, xs, cap) -> Zlen xs < cap ->
    let e := b + 4 * Zlen xs in
    let M1 := wbytes M (Z_to_bv 64 e) (word_to_le_bytes 4 u) in
    let M2 := wbytes M1 (Z_to_bv 64 (w_p w + 248)) (word_to_le_bytes 8 (Z_to_bv 64 (e + 4))) in
    PMX w A M2 model (set_v2 c (b, xs ++ [bv_unsigned u mod 2 ^ 32], cap)).
  Proof using AC MI ST.
    intros w A M model c b cap xs u X Ev2 Hroom. cbn zeta.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_v2 X) as V. rewrite Ev2 in V. cbn [t3a t3b t3c fst snd] in V.
    pose proof V as V0. destruct V0 as (V1 & V2 & V3 & V4 & Hblk & F0 & F1 & F2 & FE). unfold O_V2 in *.
    destruct Hblk as [[-> ->] | (Hb0 & Hbal & Hc0 & Hbc & HIn & Hdj)]; [lia|].
    destruct (ai_live_block MI A M model b (4 * cap) AI HIn) as (_ & _ & _ & Hbce & Hall).
    pose proof (Z.mod_pos_bound (bv_unsigned u) (2 ^ 32) ltac:(lia)) as Hx.
    set (e := b + 4 * Zlen xs). set (M1 := wbytes M _ (word_to_le_bytes 4 u)). set (M2 := wbytes M1 _ _).
    assert (SI : stores_in (fun a => zwin e (e + 4) a \/ zwin (w_p w + 248) (w_p w + 256) a) M M2).
    { unfold M2, M1. eapply stores_in_wbytes_more;
        [ apply stores_in_wbytes; [lia | w2blen; cbn; lia | intros a' Ha'; w2blen; cbn in Ha'; unfold zwin; lia]
        | lia | w2blen; cbn; lia | intros a' Ha'; rewrite length_N_to_le_bytes in Ha'; cbn in Ha'; unfold zwin; lia ]. }
    eapply (pmx_upd_foot CV2 w A M M2 model c _ _ X SI);
      [ | intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)]
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; rewrite Ev2; reflexivity |].
    - intros a [Ha|Ha]; unfold cfoot; cbn [chdr fst snd cblocks]; rewrite ?Ev2; cbn [t3a t3c fst snd].
      + right. exists (b, 4 * cap). destruct (Z.eqb_spec b 0); [lia|]. split; [left; reflexivity | cbn; unfold zwin in Ha; lia].
      + left. unfold O_V2, zwin in *. lia.
    - cbn [crep set_v2 c_v2 t3a t3b t3c fst snd]. unfold O_V2, CRep.vec32.
      assert (Hzl : Zlen (xs ++ [bv_unsigned u mod 2 ^ 32]) = Zlen xs + 1) by (unfold Zlen; rewrite length_app; cbn; lia).
      assert (OUT : forall a : word, ~ (e <= bv_unsigned a < e + 4) -> ~ (w_p w + 248 <= bv_unsigned a < w_p w + 256) -> M2 a = M a).
      { intros a H1 H2. pose proof (u64_range a). unfold M2, M1.
        rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length word_to_le_bytes Z_to_le_bytes]; lia. }
      rewrite Hzl. split; [exact V1|]. split; [exact V2|]. split; [eapply stores_in_mdef; [exact SI | exact V3]|]. split; [lia|].
      split; [right; repeat split; try assumption; lia|].
      split; [eapply fld_keep; [exact SI | exact F0 | lia | cbn; lia | unfold zwin; cbn; intros; lia]|].
      split; [replace (w_p w + 240 + 8) with (w_p w + 248) by lia; replace (b + 4 * (Zlen xs + 1)) with (e + 4) by (unfold e; lia); unfold M2; rdback|].
      split; [eapply fld_keep; [exact SI | exact F2 | lia | cbn; lia | unfold zwin; cbn; intros; lia]|].
      intros k Hk. destruct (Z.eq_dec k (Zlen xs)) as [-> | Hne].
      + rewrite Znth_app_r1.
        split; [lia|]. unfold CRep.fld, M2. rewrite rdn_wbytes_out_Z by (w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
        unfold M1. replace (b + 4 * Zlen xs) with e by reflexivity.
        rewrite <- (w2lb4_mod u).
        apply rdn_wbytes_self. w2blen. rewrite u64_of_Z by lia. cbn. lia.
      + rewrite Znth_app_l by lia. destruct (FE k ltac:(lia)) as [Hr Hf]. split; [exact Hr|].
        eapply fld_agree; [lia | cbn; lia | exact Hf |]. intros a Ha. unfold zwin in Ha. cbn in Ha. apply OUT; rewrite u64_of_Z by lia; lia.
  Qed.

  Lemma pm_ecw_pbs : forall (vc : vec_consts), TablStmts.vec32_pbslow_stmt SEGS Ly.L MI ST (2 ^ 32) vc -> vc_stack vc = 80 ->
    forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (src x ret : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    cregs w R ret -> getr R 10%bv = Z_to_bv 64 (w_p w + O_V2) -> getr R 11%bv = Z_to_bv 64 src ->
    fld SEGS M src 4 x -> 0 <= x < 2 ^ 32 -> w_sp w <= src -> src + 4 <= w_sp0 w - 104 -> src mod 4 = 0 ->
    Zlen (t3b (c_v2 c)) = t3c (c_v2 c) -> 4 * vgrow (t3c (c_v2 c)) <= 2 ^ 20 ->
    (forall A' R' M' model' (b' : Z),
        PMX w A' M' model' (set_v2 c (b', t3b (c_v2 c) ++ [x], vgrow (t3c (c_v2 c)))) ->
        pm_bud (w_n w) (set_v2 c (b', t3b (c_v2 c) ++ [x], vgrow (t3c (c_v2 c)))) ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 (b' + 4 * (Zlen (t3b (c_v2 c)) + 1)) ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (vc_entry vc) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros vc STMT Hvs w c0 K fx A M model c R src x ret PS X Htr BUD CR Ha0 Ha1 Fx Rx Hs1 Hs2 Hal Hfull Hgrow CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (cu_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS.
    pose proof (x_caps X) as (_ & _ & HNMAX). unfold LIB_NMAX in HNMAX.
    pose proof BUD as BUD'. destruct BUD' as (_ & _ & _ & _ & _ & Bv2 & _).
    destruct (c_v2 c) as [[b xs] cap] eqn:Ev2. cbn [t3a t3b t3c fst snd] in *.
    pose proof (x_v2 X) as V. rewrite Ev2 in V. cbn [t3a t3b t3c fst snd] in V.
    pose proof V as V0. destruct V0 as (_ & _ & _ & Hlen & Hblk & _).
    eapply (STMT fx A (w_s w) R M model (w_sp w) ret (w_p w + O_V2) b cap src x xs K).
    - eapply pmx_cregs_callB; [exact X | exact CR | rewrite Hvs; unfold NEW_STACK, PM_FRAME; lia].
    - exact Ha0. - exact Ha1. - exact V. - exact Hfull.
    - split; [left; unfold O_V2; lia | intros a Ha; unfold zwin, O_V2, NEW_STACK in *; lia].
    - unfold O_V2. apply mod16_8; [exact Gp16 | reflexivity].
    - exact Fx. - exact Rx.
    - split; [left; lia | intros a Ha; unfold zwin, NEW_STACK in *; lia].
    - lia. - lia. - exact Hal.
    - intros a Ha. unfold zwin, O_V2 in *. lia.
    - unfold vgrow in *. lia.
    - eapply pmx_ds_room; [exact PS | exact X | exact BUD | unfold vgrow, DS_MAXBLK in *; lia].
    - intros A' R' M' model' b' RB V' Hend LA EF. destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      pose proof V' as V1. destruct V1 as (_ & _ & _ & Hlen' & Hblk' & _).
      set (c' := set_v2 c (b', xs ++ [x], vgrow cap)).
      assert (X' : PMX w A' M' model' c').
      { eapply (pmx_updS w CV2 A M model c A' M' model' c' (vc_stack vc + NEW_STACK SEGS Ly.L MI) _ X AI' MS' FS' FDS' EF);
          [rewrite Hvs; unfold NEW_STACK, PM_FRAME; lia | | | intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)]
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; exact V' |].
        + intros a [Ha|[[Hb Ha]|Ha]].
          * left. left. unfold O_V2 in *. cbn. exact Ha.
          * left. right. exists (b, 4 * cap). cbn. rewrite Ev2. cbn. destruct (Z.eqb_spec b 0); [lia|]. split; [left; reflexivity | unfold zwin in Ha; lia].
          * right. left. right. exists (b', 4 * vgrow cap). cbn. destruct (Z.eqb_spec b' 0); [unfold zwin in Ha; lia|]. split; [left; reflexivity | unfold zwin in Ha; lia].
        + intros a [Ha|[[Hb Ha]|Ha]] Hz; exfalso; unfold zwin, O_V2, w_sp0, PM_FRAME in *; [lia | |].
          * destruct Hblk as [[-> _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hc' & _). lia.
          * destruct Hblk' as [[-> E0]|(_ & _ & _ & _ & Hl & _)]; [unfold vgrow in E0; lia|]. destruct (ai_live_block MI A' M' model' _ _ AI' Hl) as (_ & _ & _ & Hc' & _). lia.
        + eapply (live_joinS w A' c c' CV2); [intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)] | reflexivity |].
          cbn [cblocks c' set_v2 c_v2 t3a t3c fst snd].
          eapply (vec_xferS A A' M M' model model' b cap b' (vgrow cap) 4); [exact AI | exact AI' | lia | | | | ].
          * pose proof (live_splitS w A M model c CV2 X) as P. cbn [cblocks] in P. rewrite Ev2 in P. cbn [t3a t3c fst snd] in P. exact P.
          * intros Hb. destruct Hblk as [[? ?]|(_ & _ & Hc & _)]; lia.
          * right. split; [unfold vgrow; lia | exact LA].
          * intros ->. destruct Hblk' as [[_ E0]|(Hb0 & _)]; [unfold vgrow in E0; lia | lia]. }
      eapply CONT; [exact X' | | exact KEPT | rewrite Hend; reflexivity |].
      + destruct BUD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). unfold pm_bud. cbn [c' set_v2 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd].
        rewrite Ev2 in *. cbn [t3a t3b t3c fst snd] in *.
        repeat (split; [assumption|]). split; [| split; [assumption | split; assumption]]. unfold vgrow in *; lia.
      + eapply (pmx_frame_keep SEGS Ly.L MI ST ly_img_low ly_rw_img ly_errno_img); [exact X | exact EF | unfold NEW_STACK; lia |].
        intros a Ha. split; [exact Ha|]. unfold zwin, O_V2, w_sp0, PM_FRAME in *. intros [Hh|[[Hb Hh]|Hh]]; [lia | |].
        * destruct Hblk as [[-> _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hc' & _). lia.
        * destruct Hblk' as [[-> E0]|(_ & _ & _ & _ & Hl & _)]; [unfold vgrow in E0; lia|]. destruct (ai_live_block MI A' M' model' _ _ AI' Hl) as (_ & _ & _ & Hc' & _). lia.
  Qed.
  Definition pm_ecw_pbs1 := pm_ecw_pbs (ku_ecw_pbs ccU1) (cu_ecw_pbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) eq_refl.
  Definition pm_ecw_pbs2 := pm_ecw_pbs (ku_ecw_pbs2 ccU1) (cu_ecw_pbs2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) eq_refl.

  Lemma pmx_upd_own : forall (i : cix) (w : pmw MI ST) A M M' model c c' (W : Z -> Prop),
    PMX w A M model c -> stores_in W M M' ->
    (forall a, W a -> zwin (w_p w + fst (chdr i)) (w_p w + fst (chdr i) + snd (chdr i)) a) ->
    (forall j, j <> i -> csame j c c') ->
    c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c -> c_tr c' = c_tr c ->
    cblocks i c' = cblocks i c ->
    crep SEGS Ly.L MI ST w i A M' c' ->
    PMX w A M' model c'.
  Proof using AC MI ST.
    intros i w A M M' model c c' W X SI HW HS Ew Ei Ee Ef Et Eb REP.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (chdr_range i) as CR. unfold PARSER_SIZE in CR.
    assert (HWhi : forall a, W a -> alloc_ceiling <= a) by (intros a Ha; pose proof (HW a Ha); unfold zwin in *; lia).
    assert (AI' : ainv MI A M' model).
    { eapply stores_in_ainv; [exact AI | exact SI |]. intros a Ha. apply (hi_unowned MI ly_img_low ly_rw_img a AI). exact (HWhi a Ha). }
    eapply (pmx_updS w i A M model c A M' model c' 0 W X AI' (x_ms X) eq_refl eq_refl);
      [ | unfold PM_FRAME; lia | intros a Ha; left; left; exact (HW a Ha) | intros a Ha Hz; exfalso; pose proof (HW a Ha); unfold zwin, w_sp0, PM_FRAME in *; lia
      | exact HS | exact Ew | exact Ei | exact Ee | exact Ef | exact Et | exact REP |].
    - apply eff_store; [| exact (proj2 SI)]. intros a Hf _. apply (proj1 SI). exact Hf.
    - eapply (live_joinS w A c c' i HS Et). rewrite Eb. exact (live_splitS w A M model c i X).
  Qed.

  Lemma pm_v2_clear : forall (w : pmw MI ST) A M model c (b : Z),
    PMX w A M model c -> t3a (c_v2 c) = b ->
    PMX w A (wbytes M (Z_to_bv 64 (w_p w + 248)) (word_to_le_bytes 8 (Z_to_bv 64 b))) model (set_v2 c (b, [], t3c (c_v2 c))).
  Proof using AC MI ST.
    intros w A M model c b X Eb. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_v2 X) as V. destruct (c_v2 c) as [[b0 xs] cap] eqn:Ev2. cbn [t3a t3b t3c fst snd] in *. subst b0.
    assert (SI : stores_in (zwin (w_p w + 248) (w_p w + 256)) M (wbytes M (Z_to_bv 64 (w_p w + 248)) (word_to_le_bytes 8 (Z_to_bv 64 b)))) by stin.
    eapply (pmx_upd_own CV2 w A M _ model c _ _ X SI);
      [intros a Ha; cbn; unfold O_V2, zwin in *; lia | intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)]
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; rewrite Ev2; reflexivity |].
    cbn [crep set_v2 c_v2 t3a t3b t3c fst snd]. destruct V as (V1 & V2 & V3 & V4 & V5 & F0 & F1 & F2 & FE). unfold O_V2 in *.
    split; [exact V1|]. split; [exact V2|]. split; [eapply stores_in_mdef; [exact SI | exact V3]|]. split; [unfold Zlen; cbn; lia|]. split; [exact V5|].
    split; [eapply fld_keep; [exact SI | exact F0 | lia | cbn; lia | unfold zwin; cbn; intros; lia]|].
    split; [unfold Zlen; cbn [length Z.of_nat]; rewrite Z.mul_0_r, Z.add_0_r; replace (w_p w + 240 + 8) with (w_p w + 248) by lia; rdback|].
    split; [eapply fld_keep; [exact SI | exact F2 | lia | cbn; lia | unfold zwin; cbn; intros; lia]|].
    intros k Hk. unfold Zlen in Hk. cbn in Hk. lia.
  Qed.

  Lemma pm_v1_clear : forall (w : pmw MI ST) A M model c (b : Z),
    PMX w A M model c -> t3a (c_v1 c) = b ->
    PMX w A (wbytes M (Z_to_bv 64 (w_p w + 224)) (word_to_le_bytes 8 (Z_to_bv 64 b))) model (set_v1 c (b, 0, t3c (c_v1 c))).
  Proof using AC MI ST.
    intros w A M model c b X Eb. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_v1 X) as V. destruct (c_v1 c) as [[b0 n] cap] eqn:Ev1. cbn [t3a t3b t3c fst snd] in *. subst b0.
    assert (SI : stores_in (zwin (w_p w + 224) (w_p w + 232)) M (wbytes M (Z_to_bv 64 (w_p w + 224)) (word_to_le_bytes 8 (Z_to_bv 64 b)))) by stin.
    eapply (pmx_upd_own CV1 w A M _ model c _ _ X SI);
      [intros a Ha; cbn; unfold O_V1, zwin in *; lia | intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)]
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; rewrite Ev1; reflexivity |].
    cbn [crep set_v1 c_v1 t3a t3b t3c fst snd]. destruct V as (V1 & V2 & V3 & V4 & V5 & F0 & F1 & F2). unfold O_V1 in *.
    split; [exact V1|]. split; [exact V2|]. split; [eapply stores_in_mdef; [exact SI | exact V3]|]. split; [lia|]. split; [exact V5|].
    split; [eapply fld_keep; [exact SI | exact F0 | lia | cbn; lia | unfold zwin; cbn; intros; lia]|].
    split; [rewrite Z.mul_0_r, Z.add_0_r; replace (w_p w + 216 + 8) with (w_p w + 224) by lia; rdback|].
    eapply fld_keep; [exact SI | exact F2 | lia | cbn; lia | unfold zwin; cbn; intros; lia].
  Qed.

  Lemma set_scal_id : forall c, set_scal c (c_widx c) (c_icount c) (c_endian c) (c_reqconv c) = c.
  Proof using. intros c. destruct c. reflexivity. Qed.

  Lemma pm_opcode_split : forall (w : pmw MI ST) A M model c (fx : FPState) R (wv pwc pop ret : Z) K,
    PMX w A M model c ->
    getr R 10%bv = Z_to_bv 64 (PrsNeeds.sx32 wv) -> getr R 11%bv = Z_to_bv 64 pwc -> getr R 12%bv = Z_to_bv 64 pop -> 0 <= wv < 2 ^ 32 ->
    w_sp w <= pwc -> pwc + 2 <= w_sp0 w - 104 -> w_sp w <= pop -> pop + 2 <= w_sp0 w - 104 -> pwc mod 2 = 0 -> pop mod 2 = 0 ->
    getr R 1%bv = Z_to_bv 64 ret -> ret_ok (Z_to_bv 64 ret) ->
    (forall R', kept R R' ->
       let M' := wbytes (wbytes M (Z_to_bv 64 pwc) (word_to_le_bytes 2 (Z_to_bv 64 (wv / 2 ^ 16)))) (Z_to_bv 64 pop) (word_to_le_bytes 2 (Z_to_bv 64 (wv mod 2 ^ 16))) in
       PMX w A M' model c -> srealizes SEGS (cfg fx R' ret M' model) K) ->
    srealizes SEGS (cfg fx R (tc_opcode_split tcU1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w A M model c fx R wv pwc pop ret K X Ha0 Ha1 Ha2 Rw P1 P2 P3 P4 Al1 Al2 Hra Hret CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    assert (WD : forall t n, w_sp w <= t -> t + n <= w_sp w + 864 -> mdef M t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X (t + i - (w_sp w + 864 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 864 - w_STK w + (t + i - (w_sp w + 864 - w_STK w))) with (t + i) in D by lia. exact D. }
    destruct (cu_opcode_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL fx R M wv pwc pop (Z_to_bv 64 ret) Ha0 Ha1 Ha2 Rw
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Al1 Al2 (WD pwc 2 ltac:(lia) ltac:(lia)) (WD pop 2 ltac:(lia) ltac:(lia)) Hra Hret)
      as (R' & MSx & KP).
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact MSx |].
    apply (CONT R' KP). cbn zeta.
    eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M _ model c (fun a => zwin pwc (pwc + 2) a \/ zwin pop (pop + 2) a));
      [exact X | stin | unfold zwin, w_sp0, PM_FRAME; intros; lia].
  Qed.

  Lemma pm_lookup : forall (pc : Z) (nargs : nat) found hnd,
    TablStmts.lookup_shape SEGS Ly.L tcU1 pc nargs found hnd ->
    forall (w : pmw MI ST) A M model c (fx : FPState) R (x y pd ret : Z) K,
    PMX w A M model c ->
    getr R 10%bv = Z_to_bv 64 x -> 0 <= x < 2 ^ 32 ->
    (nargs = 2%nat -> getr R 11%bv = Z_to_bv 64 pd) ->
    (nargs = 3%nat -> getr R 11%bv = Z_to_bv 64 (TablStmts.sx32 y) /\ 0 <= y < 2 ^ 32 /\ getr R 12%bv = Z_to_bv 64 pd) ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    w_sp w <= pd -> pd + 8 <= w_sp0 w - 104 -> pd mod 8 = 0 ->
    getr R 1%bv = Z_to_bv 64 ret -> ret_ok (Z_to_bv 64 ret) ->
    (forall R' M' (r d : Z), kept R R' -> getr R' 10%bv = Z_to_bv 64 r -> 0 <= r < 2 ^ 64 ->
        fld SEGS M' pd 8 d -> (r = 0 <-> found x y) -> (r = 0 -> hnd d x y) ->
        PMX w A M' model c -> CRep.agree_on (fun a => w_sp w <= a < w_sp0 w /\ ~ zwin pd (pd + 8) a) M M' ->
        srealizes SEGS (cfg fx R' ret M' model) K) ->
    srealizes SEGS (cfg fx R pc M model) K.
  Proof using AC MI ST.
    intros pc nargs found hnd STMT w A M model c fx R x y pd ret K X Ha0 Rx H2 H3 Hsp P1 P2 Al Hra Hret CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (S1 & S2 & S3 & S4).
    assert (WD : forall t n, w_sp w + 864 - w_STK w <= t -> t + n <= w_sp w + 864 -> mdef M t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X (t + i - (w_sp w + 864 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 864 - w_STK w + (t + i - (w_sp w + 864 - w_STK w))) with (t + i) in D by lia. exact D. }
    destruct (STMT fx R M x y pd (w_sp w) (Z_to_bv 64 ret) (x_roc X) Ha0 Rx H2 H3 Hsp ltac:(lia) ltac:(lia) (WD pd 8 ltac:(lia) ltac:(lia)) Al
                ltac:(intros a Ha; cbn [tc_lookup_stack tcU1] in Ha; unfold zwin in *; lia)
                ltac:(unfold stack_room; cbn [tc_lookup_stack tcU1]; apply (mdef_store_ok SEGS M _ 64); [apply WD; lia | lia | lia | lia])
                ltac:(cbn [tc_lookup_stack tcU1]; lia) ltac:(lia) Gsp16 Hra Hret)
      as (R' & M' & r & d & MSx & KP & Hr & Rr & Fd & Hfound & Hhnd & FE & DK).
    cbn [tc_lookup_stack tcU1] in FE.
    pose proof (stores_in_of_frame_eq _ M M' FE DK) as SI.
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact MSx |].
    assert (Hr' : exists r', Z_to_bv 64 r = Z_to_bv 64 r' /\ 0 <= r' < 2 ^ 64 /\ (r' = 0 <-> r = 0)).
    { destruct (Z.lt_ge_cases r 0); [exists (r + 2 ^ 64); rewrite Z_to_bv64_add_mod; split; [reflexivity | lia] | exists r; split; [reflexivity | lia]]. }
    destruct Hr' as (r' & Er & Rr' & Er0). rewrite Er in Hr.
    eapply (CONT R' M' r' d KP Hr Rr' Fd ltac:(rewrite Er0; exact Hfound) ltac:(intros H0; apply Hhnd, Er0, H0)).
    - rewrite <- (set_scal_id c).
      eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact SI | | | | | | lia | lia | lia | exact S4].
      + intros a [Ha|Ha]; unfold zwin, scal_win, w_sp0, PM_FRAME in *; left; lia.
      + eapply fld_keep; [exact SI | exact (x_widx X) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | unfold O_WIDX, zwin; cbn; intros; lia].
      + eapply fld_keep; [exact SI | exact (x_icount X) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia].
      + eapply fld_keep; [exact SI | exact (x_endian X) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia].
      + eapply fld_keep; [exact SI | exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia].
    - eapply stores_in_agree; [exact SI|]. intros a [Ha Hn]. unfold zwin in *. split; [lia | lia].
  Qed.
  Definition pm_lookup_opcode := pm_lookup _ _ _ _ (cu_lookup_opcode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_lookup_operand := pm_lookup _ _ _ _ (cu_lookup_operand _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_lookup_ext := pm_lookup _ _ _ _ (cu_lookup_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
End PM.
