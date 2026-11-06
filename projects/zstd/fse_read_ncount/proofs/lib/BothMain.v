(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel TopLevelSB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg ITree Nodes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prog ProgA EquivPA AsanProgDeps AsanInv AsanOK ImgFacts AsanHandoffBoth ModelOK.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AProto.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg.
Import ListNotations.
Open Scope Z_scope.
Definition plain_tree_ok_stmt : Prop :=
forall L, 2^31 <= L ->
tree_ok psegs p_init_pc p_phdrs L
(Prog.prog psegs PREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True)).
Definition TB (L : Z) : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp (toP en)) (mo0 psegs L (toP en) inp).
Definition TP (L : Z) : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp en) (mo0 psegs L en inp).
Definition bmodelH (V : nat -> Z) (sp : word) fs (mo : Model) : Prop :=
LIMIT34 <= vm_limit (m_vmmaps mo) /\ bmodelL (vm_limit (m_vmmaps mo)) V sp fs mo.
Lemma bmodelH_of_bmodelL : forall lim V sp fs mo, LIMIT34 <= lim -> bmodelL lim V sp fs mo -> bmodelH V sp fs mo.
Proof. intros lim V sp fs mo HL HM. unfold bmodelH. rewrite (bmL_limit _ _ _ _ _ HM). split; [exact HL| exact HM]. Qed.
Definition bmain_open (en : ExecEntry) (inp : ProcInput) (w : bool) (V : nat -> Z) (m : word -> option byte)
(ms : machine_state) (mo : Model) : Prop :=
let usp := bv_unsigned (en_sp en) in
let argc := Z.of_nat (length (in_argv inp)) in
let envc := Z.of_nat (length (in_envp inp)) in
ms = MS (mkR (Z_to_bv 64 BRA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 BGP) (Z_to_bv 64 BTP)
(Z_to_bv 64 (V 1336%nat)) (Z_to_bv 64 (V 1337%nat)) (Z_to_bv 64 (V 1338%nat))
(Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
(Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
(Z_to_bv 64 (V 1339%nat)) (Z_to_bv 64 (V 1340%nat)) (Z_to_bv 64 (V 1341%nat)) (Z_to_bv 64 (V 1342%nat))
(Z_to_bv 64 BMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
(Z_to_bv 64 (V 1343%nat)) (Z_to_bv 64 (V 1344%nat)) (Z_to_bv 64 (V 1345%nat)) (Z_to_bv 64 (V 1346%nat)))
bvmap_empty (Z_to_bv 64 BMAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)
/\ (forall n, 0 <= V n < 2 ^ 64)
/\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
/\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
/\ V 1%nat = argc /\ V 2%nat = envc
/\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
/\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
/\ V 9%nat = bv_unsigned (in_hwcap inp))
/\ Forall (mfact_ok bsegs V m) (both_mem_facts ++ both_mem_facts_w w)
/\ Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w)
/\ mem_inv bsegs m
/\ stk bsegs m (usp - 8388608) usp
/\ (forall a, hidden_arg en inp a ->
m (wa a) = wrap_mem b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (wa a))
/\ bshadow0 V m
/\ bmodelH V (en_sp en) (in_fs inp) mo.
Lemma bmain_atL_open : forall lim en inp ms mo, LIMIT34 <= lim ->
bmain_atL lim en inp ms mo -> exists w V m, bmain_open en inp w V m ms mo.
Proof.
intros lim en inp ms mo HL (w & V & m & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). exists w, V, m.
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 _))))))))).
exact (bmodelH_of_bmodelL lim _ _ _ _ HL H10).
Qed.
Lemma bmain_at_open : forall en inp ms mo,
bmain_at en inp ms mo -> exists w V m, bmain_open en inp w V m ms mo.
Proof.
intros en inp ms mo HM. apply (bmain_atL_open target_alloc_limit); [| apply bmain_at_bmain_atL; exact HM].
rewrite <- LIMIT_eq. apply LIMIT34_le_LIMIT.
Qed.
Definition both_impl_stmt (rsA : Z) : Prop :=
forall en inp w V m ms mo,
valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
bmain_open en inp w V m ms mo ->
exists NMAX RNG A Q,
tree_atA bsegs (at_nodeA bsegs) nstepA minvA (nsafeA NMAX) fstepS NMAX RNG A
(progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp)))
Q ms (MX mo []) mo.
Section Assembly.
Variable rsA : Z.
Hypothesis plain_ok : plain_tree_ok_stmt.
Hypothesis both_impl : both_impl_stmt rsA.
#[using="plain_ok"] Lemma plain_side_ok : forall L, 2^31 <= L -> side_ok psegs p_init_pc p_phdrs L (TP L).
Proof. intros L HL. exact (side_ok_of_tree_ok _ _ _ _ _ _ (plain_ok L HL)). Qed.
#[using="rsA both_impl"] Lemma both_main_srealizes : forall L, 2^31 <= L -> forall en inp,
valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
forall ms mo, (exists w V m, bmain_open en inp w V m ms mo) -> SpinAlg.srealizes bsegs (mkCfg ms mo) (TB L inp en).
Proof.
intros L HL en inp Hv Hi ms mo (w & V & m & HM).
pose proof HM as (_ & _ & _ & _ & HP & _ & _ & _ & _ & [HLIM HMOD]).
apply Forall_app in HP as [HP _].
destruct (both_impl en inp w V m ms mo Hv Hi HM) as (NMAX & RNG & A & Q & HT).
eapply SpinAlg.srz_conseq.
+ exact (implF_srealizes bsegs (at_nodeA bsegs) nstepA nexitA minvA (nsafeA NMAX) fstepS NMAX (nodesA_sound bsegs NMAX) _ RNG A Q ms (MX mo []) mo HT).
+
destruct (equiv_PA_both_toP_LL (vm_limit (m_vmmaps mo)) HLIM L HL PREAD_STAGE rsA V (en_sp en) _ _ _ en inp mo Hv Hi HMOD HP) as [HEQ _].
intros tr. unfold TB. symmetry. apply HEQ.
Qed.
#[using="rsA plain_ok both_impl"] Lemma both_side : forall L, 2^31 <= L -> side_ok bsegs b_init_pc b_phdrs target_alloc_limit (TB L).
Proof.
intros L HL. apply both_side_ok. intros en inp Hv Hi. split.
-
destruct (plain_side_ok L HL (toP en) inp (toP_valid _ _ _ en inp Hv) Hi) as [Htr _].
apply Htr. rewrite run_init_config. cbn [bh_traces]. apply obs_trace_cfg_nil.
- intros ms mo HM. apply bmain_at_open in HM. exact (both_main_srealizes L HL en inp Hv Hi ms mo HM).
Qed.
#[using="rsA plain_ok both_impl"] Theorem base_both :
strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
(mkImage psegs p_init_pc p_phdrs)
(mkImage bsegs b_init_pc b_phdrs).
Proof.
eapply (side_ok_equiv_sb _ _ _ _ _ _ (TP sanitizer_source_limit) (TB sanitizer_source_limit));
[exact (plain_side_ok _ lim_sb) | exact (both_side _ lim_sb) |].
intros enS enT inp HvS HvT Hi. unfold TP, TB.
apply (equiv_PP_L _ lim_sb); [exact HvS | exact (toP_valid _ _ _ enT inp HvT) | exact Hi].
Qed.
End Assembly.
