(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit Stdio_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AHarness_bm () := "C46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7hinv_bmC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03c5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_LOc5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm7AHBM_HIC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFI47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4appWK46Stdlib9micromega6VarMap1t01C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kitDappW_shadow_disjointC5ARocqVerifyHarness?AgentSubmission4LibA6ShadowBshadow_bytes_munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission4LibA6ShadowBshadow_bytes_agreeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC47Corelib4Init5Logic6eq_indC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeI47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface;shad_unshadC47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:aheap_presc5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm>hinv_bm_client".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Section CANSEC1. Context {rc : runConstT}.
Definition AHBM_LO : Z := 0x20ea0.     (* [comment removed for export] *)
Definition AHBM_HI : Z := 0x20f20.

(* [comment removed for export] *)
Definition hinv_bm (m : amem) : Prop := shadow_bytes m (shad AHBM_LO) (shad AHBM_HI) (fun _ => 0).

Lemma hinv_bm_zero : forall m a, hinv_bm m -> AHBM_LO <= a < AHBM_HI -> m (wa (shad a)) = Some (Z_to_bv 8 0).
Proof.
  intros m a (_ & _ & H) Ha. apply H. rewrite !shad_div. unfold AHBM_LO, AHBM_HI in *.
  (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
Qed.

(* [comment removed for export] *)
Lemma hinv_bm_munch : forall W m m', hinv_bm m -> munch W m m' -> appW W -> hinv_bm m'.
Proof.
  intros W m m' H HW HA. unfold hinv_bm in *. eapply shadow_bytes_munch; [exact H| exact HW|].
  apply appW_shadow_disjoint; [exact HA| unfold AHBM_LO; lia| unfold AHBM_HI, KEND; lia].
Qed.

(* [comment removed for export] *)
Lemma hinv_bm_magree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, shad AHBM_LO <= a < shad AHBM_HI -> P a) ->
  hinv_bm m -> hinv_bm m'.
Proof.
  intros P m m' HG HP H. unfold hinv_bm in *. eapply shadow_bytes_agree; [exact H|].
  intros s Hs. destruct H as (H0 & H1 & _). exact (proj1 (HG s ltac:(lia) (HP s Hs))).
Qed.

(* [comment removed for export] *)
Lemma hinv_bm_client : forall CI LB SP a, (forall x, AHBM_LO <= x < AHBM_HI -> in_ranges CI x) ->
  shad AHBM_LO <= a < shad AHBM_HI -> aclient_addr CI LB SP a.
Proof.
  intros CI LB SP a HC Ha. right; right; right. exists ((a - ASHOFF) * 8). split.
  - right; left. apply HC. rewrite !shad_div in Ha. unfold AHBM_LO, AHBM_HI in *.
    (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  - rewrite shad_div, Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma hinv_bm_pres : forall CI LB SP m m', aheap_pres CI LB SP m m' -> (forall a, AHBM_LO <= a < AHBM_HI -> in_ranges CI a) ->
  hinv_bm m -> hinv_bm m'.
Proof.
  intros CI LB SP m m' HP HC H. unfold hinv_bm in *. eapply shadow_bytes_agree; [exact H|].
  intros s Hs. destruct H as (H0 & H1 & _). exact (proj1 (HP s ltac:(lia) (hinv_bm_client CI LB SP s HC Hs))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FuzzOneB.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Definition fuzz_oneA_stmtB : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (D : Z) (payload : list Z) (lo : Z) (rstk : region),
      AHEAP AI L RNG (aps_m s) LB m ->
      (* [comment removed for export] *)
      (forall b, In b LB -> exists p A n, b = HB p A n) ->
      (* [comment removed for export] *)
      payload_atA LB D payload ->
      bytes_at bsegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      D mod 16 = 0 -> zlength payload < 2^26 ->
      (* [comment removed for export] *)
      harness_invA m ->
      (* [comment removed for export] *)
      hinv_bm m ->
      (* [comment removed for export] *)
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
      bv_unsigned sp + ATRUN_DEPTH = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->
      (* [comment removed for export] *)
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
      s0 = Z_to_bv 64 (zlength payload) ->
      mem_inv bsegs m -> frm0 fc ->
      tp = Z_to_bv 64 ATP ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) -> ra = Z_to_bv 64 ATRUN_RET ->
      (* [comment removed for export] *)
      HU L ->
      (* [comment removed for export] *)
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
      (* [comment removed for export] *)
      aps_ok L s ->
      implMA RNG (fuzz_oneA AAllocAsan payload) s
             (fuzz_oneA_post AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom bsegs)).
End FuzzOneB.
End CANSEC1.
