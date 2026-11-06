(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoffBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ AFake_iface AFake_init
ADepot_iface ADepot ADepot_init F_adepot ARepInit_kit ARepInit_A ARepInit_B ARepInit_C ARepInit_D ARepInit_E.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Section Init.
Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.
Hypothesis SH0 : bshadow0 V m.
Let L := mkALayout (LV V) w U.
#[using="rc HM HP HU HAT"] Theorem AQUAR_init : AQUAR L (ST0 V) X0 m.
Proof.
exists qconc0. unfold AQUAR_at. cbn [q_loc q_glob q_ia qconc0 a_qloc a_qglob a_qloc_bytes a_qglob_bytes ST0 ainit].
split; [exact (aquar_glob_const_init V m HM)|].
split; [exact (aqcache_loc_init V w U m HM HP HU HAT)|].
split; [exact (aqcache_glob_init V w U m HM)|].
split; [exact (aintal_init V m HM)|].
split; [exact (qcoupled_init L V)| exact (qnum_init V)].
Qed.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HQ : AQ L (ST0 V) X0 m.
Hypothesis HS : ASEC L (ST0 V) X0 m.
Hypothesis HD : DEP L m.
Let H := mkAHoles AQ ASEC DEP AFK.
#[using="HM HP HU HAT SH0 HQ HS HD"] Theorem AREP_init : AREP H L (ST0 V) X0 m.
Proof.
unfold AREP. cbn [ah_quar ah_sec ah_depot H].
split; [exact (awf_init V w U HP HU HAT)|].
split; [exact (arep_rt_init V w U m HM)|].
split; [exact (ainstance_init V w U m HM)|].
split; [exact (athread_init V w U m HM HP HU HAT)|].
split.
{ intros c Hc. split; [exact (aregion_cells_init V w U m HM HP HU HAT c Hc)|]. split; [exact (afreearray_init V w U m HP HU HAT c Hc)|].
split; [exact (aslots_init V w U m HP HU HAT c Hc)| exact (aslot_shadow_init V w U m HP HU HAT c Hc)]. }
split; [exact HQ|]. split; [exact HS|]. split; [exact HD|].
split; [exact (arelro_init V m HM)|].
split; [exact (arep_rt2_init V m HM)|].
split; [intros c Hc; exact (ashadow_avail_init V w U m HP HU HAT SH0 c Hc)|].
exact (arep_rt3_init V m HM).
Qed.
Variables (lz : list (word * word)) (AL : word -> Prop).
Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V both_vis) p -> AL p.
Hypothesis ASH0 : forall (p : word) (c k : Z), bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->
(bv_unsigned p = shad (al_space_beg L) + 536870912 * c - 4096
\/ (0 <= k <= 14336 /\ bv_unsigned p = shad (al_space_beg L) + 536870912 * c + 32768 * k)) -> AL p.
Hypothesis HF : AFK L [] m.
#[using="HM HP HU HAT SH0 HQ HS HD A0I ASH0 HF"] Theorem AHEAP_P_init : AHEAP_P H L (fp_ok lz AL) (ST0 V) [] m.
Proof.
split; [exact (alayout_ok_init V w U HP HU HAT)|].
split; [exact (arng_init lz AL V w U A0I HP HU HAT ASH0)|].
split; [exists X0; split; [exact AREP_init| exact (ablocks_init L _)]|].
exact HF.
Qed.
End Init.
#[using="Type"] Corollary AHEAP_P_init_fake :
forall (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop)
(V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
Forall (mfact_ok bsegs V m) both_mem_facts -> Forall (pfact_ok V) both_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP -> bshadow0 V m ->
AQ (mkALayout (LV V) w U) (ST0 V) X0 m -> ASEC (mkALayout (LV V) w U) (ST0 V) X0 m -> DEP (mkALayout (LV V) w U) m ->
(forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V both_vis) p -> AL p) ->
(forall (p : word) (c k : Z), bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->
(bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c - 4096
\/ (0 <= k <= 14336 /\ bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c + 32768 * k)) -> AL p) ->
AHEAP_P (mkAHoles AQ ASEC DEP AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
intros AQ ASEC DEP V w U m lz AL HM HP HU HAT SH0 HQ HS HD A0I ASH0.
apply AHEAP_P_init; try assumption. apply afake_init; assumption.
Qed.
#[using="Type"] Corollary AHEAP_P_init_quar_fake :
forall (ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop)
(V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
Forall (mfact_ok bsegs V m) both_mem_facts -> Forall (pfact_ok V) both_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP -> bshadow0 V m ->
ASEC (mkALayout (LV V) w U) (ST0 V) X0 m -> DEP (mkALayout (LV V) w U) m ->
(forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V both_vis) p -> AL p) ->
(forall (p : word) (c k : Z), bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->
(bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c - 4096
\/ (0 <= k <= 14336 /\ bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c + 32768 * k)) -> AL p) ->
AHEAP_P (mkAHoles AQUAR ASEC DEP AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
intros ASEC DEP V w U m lz AL HM HP HU HAT SH0 HS HD A0I ASH0.
apply AHEAP_P_init_fake; try assumption. apply AQUAR_init; assumption.
Qed.
#[using="Type"] Corollary AHEAP_P_init_qdf :
forall (ASEC : alayout -> astate -> aconc -> amem -> Prop)
(V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
Forall (mfact_ok bsegs V m) both_mem_facts -> Forall (mfact_ok bsegs V m) (both_mem_facts_w w) -> Forall (pfact_ok V) both_pure_facts ->
(length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U ->
32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP -> bshadow0 V m ->
ASEC (mkALayout (LV V) w U) (ST0 V) X0 m ->
(forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V both_vis) p -> AL p) ->
(forall (p : word) (c k : Z), bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->
(bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c - 4096
\/ (0 <= k <= 14336 /\ bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c + 32768 * k)) -> AL p) ->
AHEAP_P (mkAHoles AQUAR ASEC (ADEPOT adepot_iface) AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
intros ASEC V w U m lz AL HM HMw HP HU HU' HAT SH0 HS A0I ASH0.
apply AHEAP_P_init_quar_fake; try assumption. cbn [ADEPOT adepot_iface]. apply adepot_init; assumption.
Qed.
End CANSEC1.
