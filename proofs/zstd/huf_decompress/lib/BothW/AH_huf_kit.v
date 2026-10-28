(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AProg_kit AHarness_iface AKit FsKit Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AH_huf_kit () := "C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appC45stdpp;list_basics4list9app_inj_1C46Stdlib5Lists4List8flat_mapI46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List:firstn_nilI5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<AMallocIface00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_relroC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C47Corelib4Init9Datatypes6lengthK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem:rw_bytes_bK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01C56Stdlib6ZArith6BinInt1Z3powK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rw_cells_image0K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure?rw_cells_recastC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW5ABase9ARELRO_LOC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9ARELRO_HIC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_rtcellsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8artcellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04I47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2or00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01K47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFK47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_sp0c5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kitApage_round_up_geFK46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface;ATRUN_DEPTHc5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit?fse_rt_of_aheapc5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit6fse_rtc5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit@fse_got_of_aheapc5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit5aboveC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kitAdisjoint_of_aboveC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorI47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=length_firstnC56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C46Stdlib5Lists4List@nth_error_firstnC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?magree_of_munchC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree;magree_monoC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree<magree_transC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase9lb_removeC5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kit?lb_remove_headAC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_kindC46Stdlib5Lists4List>NoDup_cons_iffC46Stdlib5Lists4List;in_flat_mapC46Stdlib5Lists4List:in_app_iffC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6decideC45stdpp;list_basics4list;list_filterC35stdpp4base6filterI47Corelib4Init6Specif7sumbool00C56Stdlib6NArith6BinNat1N8eqb_specC56Stdlib6NArith6BinNat1N3eqbI47Corelib4Init9Datatypes7reflect00C45stdpp;list_basics4list;filter_consC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6hb_idsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase:abkind_eqbC47Corelib4Init9Datatypes4negbI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind00I47Corelib7Numbers7BinNums1N00K47Corelib4Init9Datatypes4bool02C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rhiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit7shcleanC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6hull64C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7app_blkC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface;shad_unshadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow@unpoisoned_agreeC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree<wr_at_magreeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDI5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase>ablk_disj_bandC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSc5ARocqVerifyHarness?AgentSubmission5BothW:AH_huf_kit9cl_shadow".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AGOT_SUAR5 : Z := 0xb2180.    (* [comment removed for export] *)
Definition ASUAR5 : Z := 0xba300.

Lemma fse_got_of_aheap : forall (AI : AMallocIface) L RNG st LB m, AHEAP AI L RNG st LB m ->
  rw_cells bsegs m 0xb2180 [C8 (Z_to_bv 64 0xba300)] /\ rw_cells bsegs m 0xb2148 [C8 (Z_to_bv 64 0xb3fa8)].
Proof.
  intros AI L RNG st LB m AH. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold ARELRO_LO, ARELRO_HI in R.
  split.
  - eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m 0xb2180 (le8 (Z_to_bv 64 0xba300)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
  - eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m 0xb2148 (le8 (Z_to_bv 64 0xb3fa8)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma fse_rt_of_aheap : forall (AI : AMallocIface) L RNG st LB m, AHEAP AI L RNG st LB m ->
  rt_got m /\ rt_got_ric m /\ rt_real_mem m /\ rt_shbase m /\ rw_cells bsegs m 0xba300 [C4 (Z_to_bv 64 1)] /\ rt_inited m /\ rt_layout m.
Proof.
  intros AI L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & A & B & C & D & E & F & G & _).
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact F| exact G].
Qed.

End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1b. Context {rc : runConstT}.
Lemma cr_stack : forall CI LB SP A n, SP <= A -> A + n <= 2^47 -> aclient_range CI LB SP A n.
Proof. intros. left. left. split; assumption. Qed.

Lemma cr_block : forall CI LB SP A n b, In b LB -> ab_addr b <= A -> A + n <= ab_addr b + ab_size b -> aclient_range CI LB SP A n.
Proof. intros CI LB SP A n b Hb H1 H2. right. left. exists b. split; [exact Hb| split; assumption]. Qed.

End CANSEC1b.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FZRB13 (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma FZRB13_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  cells_size (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 104%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma page_round_up_geF : forall x, 0 <= x -> x <= page_round_up_Z x < x + 4096 /\ page_round_up_Z x mod 4096 = 0.
Proof. intros x Hx. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

Lemma harness_topF : forall L SP, SP + ATRUN_DEPTH = al_sp0 L -> 0 <= SP -> SP + 16 <= al_top L < SP + 48 + 4096.
Proof.
  intros L SP E H0. unfold al_top. rewrite <- E. unfold ATRUN_DEPTH. replace (SP + 208 - 160) with (SP + 48) by lia.
  pose proof (page_round_up_geF (SP + 48) ltac:(lia)). lia.
Qed.

End CANSEC2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
Definition fse_rt (m : amem) : Prop :=
  rt_got m /\ rt_got_ric m /\ rt_real_mem m /\ rt_shbase m /\ rt_inited m /\ rt_layout m
  /\ rw_cells bsegs m 0xb2148 [C8 (Z_to_bv 64 0xb3fa8)].

Lemma fse_rtall_of_aheap : forall (AI : AMallocIface) L RNG st LB m, AHEAP AI L RNG st LB m -> fse_rt m.
Proof.
  intros AI L RNG st LB m AH. destruct (fse_rt_of_aheap AI L RNG st LB m AH) as (A & B & C & D & _ & F & G).
  destruct (fse_got_of_aheap AI L RNG st LB m AH) as [_ H].
  exact (conj A (conj B (conj C (conj D (conj F (conj G H)))))).
Qed.

Fixpoint above (lo : Z) (W : list (Z * Z)) : Prop :=
  match W with [] => True | (a, b) :: W' => lo <= a /\ above lo W' end.

Lemma disjoint_of_above : forall W A n, above (A + n) W -> 0 <= n -> disjoint_from W A n.
Proof. induction W as [|[a b] W IH]; intros A n H N; cbn in *; [exact I|]. destruct H as [H1 H2]. split; [lia| apply IH; assumption]. Qed.

Lemma fse_rt_munch : forall W m m', fse_rt m -> munch W m m' -> wmono bsegs m m' -> above AIMG_HI W -> fse_rt m'.
Proof.
  intros W m m' (A & B & C & D & E & F & G) MU WM AB.
  assert (T : forall X cs, rw_cells bsegs m X cs -> X + Z.of_nat (cells_size cs) <= AIMG_HI -> rw_cells bsegs m' X cs).
  { intros X cs H HX. eapply rw_cells_transport; [exact H| exact MU| exact WM|]. apply disjoint_of_above; [| lia].
    clear - AB HX. induction W as [|[a b] W IH]; cbn in *; [exact I|]. destruct AB as [A1 A2]. split; [lia| apply IH; exact A2]. }
  unfold AIMG_HI in T.
  refine (conj (T _ _ A _) (conj (T _ _ B _) (conj (T _ _ C _) (conj (T _ _ D _) (conj (T _ _ E _) (conj (T _ _ F _) (T _ _ G _))))))); cbn; lia.
Qed.
End CANSEC3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT}.
Lemma bytes_at_firstnF : forall m A bs n, bytes_at bsegs m A bs -> (n <= length bs)%nat -> bytes_at bsegs m A (firstn n bs).
Proof.
  intros m A bs n (H0 & H1 & HB) Hn. split; [exact H0|]. split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [| lia]. apply HB. lia.
Qed.

End CANSEC4.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC5. Context {rc : runConstT}.
Lemma aca_monoA : forall CI LB LB' SP SP' a, aclient_addr CI LB SP a -> (forall b, In b LB -> In b LB') -> SP' <= SP -> aclient_addr CI LB' SP' a.
Proof.
  intros CI LB LB' SP SP' a Ha HL HS. unfold aclient_addr, in_block, in_fake in *.
  destruct Ha as [X|[X|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - left; lia.
  - right; left; exact X.
  - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  - right; right; right. exists a'. split; [|reflexivity].
    destruct Ha' as [X|[X|(c & A & n & Hin & X)]]; [left; lia| right; left; exact X| right; right].
    exists c, A, n. split; [apply HL; exact Hin| exact X].
Qed.

Lemma cl_stack : forall CI LB SP a, SP <= a < 2^47 -> aclient_addr CI LB SP a.
Proof. intros CI LB SP a H. left. exact H. Qed.
Lemma cl_block : forall CI LB SP b a, In b LB -> ab_addr b <= a < ab_addr b + ab_size b -> aclient_addr CI LB SP a.
Proof. intros CI LB SP b a Hb Ha. right; right; left. exists b. split; [exact Hb| exact Ha]. Qed.
Lemma cl_shadow : forall CI LB SP a', ((ATOP <= a' < 2^47) \/ in_ranges CI a' \/ in_fake LB a') -> aclient_addr CI LB SP (shad a').
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_kit ()) ["CANSEC5"] "h02a'h12CIh21Hh32LBh42SPp;2p;1p;3p;4g0126j2DTg007nj1;Tg016Aj1=Tg00E[j24Tg008Nj1CTg00>@j19Tg00NBj12Tg00TEj2<Tg00GMj25Tg00Gij21Tg01g@j23Tg01j1j28Tg0181j20Tg01fHj16Tg01i8j2BTg00=fj3:Tg015gj2ATg00HDj2@Tg00VEj4?Tg01<Kj4>Tg01<ej37Tg00^WR0/D0#;g00fO#;p,2rc#=R1f0R2'4g00gH#CR3#9%23#2#2#2#9'<R3,52'1R4f3R5/32f2R6/82'0'0f1R7#6R8,461583'1f4R9/38R:1B58R;f5/321892'0,04%66%625:0'1X00R6,A0R4'0R<'0P0P6P714171573'113971857'0'0A:088P21@08C?C>97;497:<37W2X00X40W3W1o"). Qed.

(* [comment removed for export] *)
Lemma magree_munch_step : forall (P : Z -> Prop) m mx my W,
  magree bsegs P m mx -> munch W mx my -> wmono bsegs mx my -> (forall a, P a -> outside W a) -> magree bsegs P m my.
Proof.
  intros P m mx my W MG MU WM HP. eapply magree_trans; [exact MG|].
  eapply magree_mono; [eapply magree_of_munch; [exact MU| exact WM]|]. exact HP.
Qed.

(* [comment removed for export] *)
Lemma stack_not_client : forall CI LB SP X a,
  (forall iv, In iv CI -> snd iv <= AIMG_HI) -> (forall iv, In iv CI -> 0 <= fst iv) ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  ATOP <= X -> X <= a < SP -> ~ aclient_addr CI LB SP a.
Proof.
  intros CI LB SP X a HCI HCI0 HLB HX Ha. pose proof atop_range as ATR.
  unfold aclient_addr, in_ranges, in_block, in_fake. intros [Y|[(iv & Hiv & H1 & H2)|[(b & Hb & H1)|(a' & Ha' & E)]]].
  - lia.
  - pose proof (HCI iv Hiv). unfold AIMG_HI in *. lia.
  - pose proof (HLB b Hb) as HB. apply ablk_lin in HB. lia.
  - rewrite shad_div in E. unfold ASHOFF in E.
    assert (0 <= a' < 2^47).
    { destruct Ha' as [Y|[(iv & Hiv & Y1 & Y2)|(c0 & A0 & n0 & Hin0 & Y1)]].
      - lia.
      - pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
      - pose proof (HLB _ Hin0) as HB. cbn in HB. apply ablk_lin in HB. lia. }
    Z.div_mod_to_equations; lia.
Qed.
End CANSEC5.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC6. Context {rc : runConstT}.
Lemma lb_remove_midA : forall p A n pre post, List.NoDup (hb_ids (pre ++ HB p A n :: post)) ->
  lb_remove p (pre ++ HB p A n :: post) = pre ++ post.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_kit ()) ["CANSEC6"] "p'0h01qh11Hh22NDh31Nh41Ah51lh61Eh71ai001ah81bi011bh91xi021xh:2NBh;2bAh<2bnh=4posth>2NIh?1ei031eh@3prehA2q'hB1BhC2H0hD7ab_addri047ab_addrhE7ab_kindi057ab_kindhF7ab_sizei067ab_sizehG1chH1fhI2l'hJ1yhK2H1hL2IHhM3ND'hN3ND1hO1YhP2_HhQ1ni071nhR2n0hS1pi081phT1ri091rhU1si0:1si0;3clsi0<1ip%0p;1p;3p;2p;5p;6p;4p;8p;7g007nj1MTg024dj10Tg01:>j38Tg025]j2HTg00=fR0j39Tg00@9j1YTg026Wj5bTg027[j15Tg00@Yj3Gj2jTg004Oj3@Tg00GiR1j23Tg005lR2j2ETg013`j31Tg01=`j12Tg028Sj3dTg002Uj6cTg005OR3j4JTg015gS00j2PTg0296j5aTg0181j2XTg029Vj4`Tg00HDj2LTg01;7j3WTg01<ej3_Tg00VEj4NTg01<Kj4^Tg003Oj8rj6]j7qTg019Ej1FTg001>j6pTg02:5j2VTg02:Tj1ITg02:oj1RTg02;Mj2nTg02;aj1mTg02<Fj6TTg02<ZR4j2lTg0032j8iTg02=:j2hTg02=\j2[Tg02>9S01j2gTg02>\j5fTg003mj5kTg02?Aj1eTg02@8j2\Tg02A3j1UTg00fOR5f2R6f1R7f0R85G53@p=7g0000R9%e8'Ep==%06?878p=CA@578p=>AG578p=:P5P9P7P8CJp=K1E98p=;g02AQR:?978p=6A9978,36p=S1P98#2p=<P5P9f5R;f4R<f3R=?867=G585@5CJp=BA1978p=DA9978p=4A9:67/38p=A1P98p=ZA8=67=G58p=o1\78#Up=O1\78#U#Ip=?%U8#Ip=Qg00^WR>%M5R?P5%0;S02?8<=R@=778#=f6RAACA;<RB=767'H1>67RC59?[^=?X@?%Y5RDAC<=6RE;78#=P;P<P=P7P8DbA7D@7,H;1>D759?eW2X=?A77B8#=f7RB%0BRD?8A;RF=767'H=9?C[^=?1:=6?7F8#=P5P:%M9RF%58RC%Y9RG9G98RHPGn011020002101081010;RIPIX85RJf9RKf8RL;CB=7<6RM'K5@9#;f:RN#0RO?8KL=7;=RP,KJ#;%56S03%08RQ'6RRf;RS7S8X09#<'3]2P<P:P:PFA8678RT#5PHPGn011020002101081010;PJPNf?RU#0RVf>RWf=RXPLEB5@9#;f@RY#0RZ?8UW=7SKS04,KJR[#;A8<=6#5R\/6QR]fAR^7S8X09#<'3]2^F>^D>P8P:PFAC678R_#5PHPGn011020002101081010;=@9[#;P2p4p710R2%M7R`P1AG678,E6A1=67#21E=7'3[RaA1678#21E68'3AG=67,E=Rb[A1<=6#21E<6'3\bAd678P7n2001000000120000000W5X78W4Pa^5`^78^42P8P9P<PJPXfBR2#0RaP^PYPSEBRbP7O41D<b#2%;b'3P1PJPWfCRb#0RcP2P^f<RdEBRe,D;#2%;ePJPUfDRe#0RfPbP2PXEB#;fERg,48Rh9ADQX09#<'3P8PJPY%0gRDPePbPWEB,DB#2PJP^fFRi#0PgPePUEB#;fGRe?Cig=72YRj,KJ#;fHRk,489AOQX09#ZRl#2S05P8Q00P9%0SRm/6QRnfIRo,48Rp'3X09g01J;RqP8%0XRrfKRs,487AQP1%0WRW%07Rt'6fLRu,47PqP8%0=Rv,6ZfORZ,4<P9fPRw16cQPq]6XA9%0w,6aP0P:PcfSR0#0Ra,67Pq[P8fQRx#0S06,6cfRRy#0Rz,6fP:P9P:P9P8P8Pen011000002101081010;X?:PDPaP8Ec14g0fTRg,4iP8fURa,4eP9fVRDPqX79P9PDPJPyfWR{#0R|PDPaPwEB,D8#2fXR}#0,6tPq]6]>X09PJPx%0DPaPgPZEB,DD#216||P7P3p4p710R|P3p4p7210R3P`\7RD%M6RZP1P<P=P6P7CJ91=8A1A8=P<P8O191;6'3X9;,P;R~[A1;86P=P8O191<7'3X9<,P<P;P<P=P6CJ91<7[S07PAP;P<P=CJ91;6\~P<P=P6P7P8DaP8n2001000000120000000XJ6W5WHWBW4Q07^J6^5Z^HD^B3^4|P8P5P9PJfYR|?C}{R{=7gyRgP|P5fZRy?C|}R}/:0R3,>a91581DyI'3X95P{A15{gP:PF%5{PHPGn011020002101081010;,D|R{g001Zp4p710Rg%M8RyP1A@=6791=8A1<7=A1<76'XRI[A1=86A1=87'XA@<=691<7[RDA@;<=91;6\IP=P6P7P8C`P8n2001000000120000000X76XI`W5W4PD^76^I`^5y^4gP8P5PaP3P}A15}aA15}3A95}}A15}01L5}3W3_O5b114||1L9|7WqP{eCNC^O6b1O1W6W>PkP7PYP;GrPkP8E]bKWCP8O1bCW1P8O1W1n2002100000000101168zPq[X7:Q06O1P81L:zO1b1W6P;P8P7FqW1W6P7P8O2n2001000000121000000W1XA9P7P8O2n2001000000121102000X1lQ05eCNW2W>P7P8O2n2001000000121000000b2b1%0^Rl?8YU=7dNRY,KJ#;RJ%5ERE/6QRU1482R2'3X09#<'3eW2X<>X;>X09P8O1P:PF%F6?878RF#5PHPGn011020002101081010;=@9[#;PJ%F<R[?AQ2X09#ZRG#2RHP8Q00P9%F;Rz148bR{7AQX09PqP8%FB?AQhP1%FL/6t147iPqP8%FN/6v14<oP:%FdP:p-0P8Pqg00mXn011000002101081010;X?:g00n4RvQ02P7EpPq1Vq8b1WPW6P7P8O2n2001000000120000000W1XA9P7P8O2n2001000000120102000X1GPHeCNA8[=6#5R[/6QRH/32X09#<,3JeW2X<>X;>XG>P8O1n011000002111081110;XE:P6P7P8O3n01100000131105104106P8O1%0LPBPAP7CoRJ,>=#=%5;148K7AQX09#<'3R2eP2P1%=M%5A148N7AQX09#<1:AP,HN1>;=,:A59?P8A8mNK=7A<#=%5KRm148X7AQX09#<P?P41OmrRm#IRQ%2QRPP?%Rm,nQRmP5P?%m5RM1OCVR1#IX85%R1X95A8WXd=7KBETR1,:NP1n2001000000210000100001>KB,:N99?8X5?Pm1lQPP4%5N/?WRP%2PP4%5S/?VRV%2VR4P?P8P5P?PM1OClRl#IX85%RlX95Q04ETRl,:dPln2001000000210000100001>NL,:S59?P8P?P?1j5dRPPPPl1>SKRQP?\?/LPPNPKP<O2GiXOVP8O11:dQ99?lP8P51:8Y#=13R{X09#<Q03/?c#2%5=/?f]3]:]2PdP:1:Tj#=13]pX09#<%0o,?\#2A8;<=#5fJR\#0Ro'?]3]:]2^F>^D>P8ACkei=7b^Rb,:_#=148\R\,3UX09#<1?Eo#21h;sg02BJRE?9;s1[;s'g1[Aug00baQ01fM99EB%Q7#2%Q6]3P7fN99ELREg00cA#QRB#2PAP9ASn8xX09PN16OO14Nw1L:OP7CNC^O1,VBW3W?P8O1%2Eg02Bh#Q#2PvW3WRP8O1n10210110900021010310107P6O1b8bT%5@%0sRs'?eW3W:W2X<>X;>X09P8O11:Fb#=13H\X09#<1?[o#2PvA8z<=#5/?seW3W:W2X<>X;>XG>P8O1n011000002101081010;XE:P6P7P8O3n01100000131105104106PLP=P8O3O1'VX34P8O1n200110:00021010<11107bUP5P?PM1OCWRW#IX85RC%RWX95RWA8rdS=7LARr,:KRdETP5PCPWPKPrDfE]1HXd1>LA,:K59?eW:WNP7P8O2n2001000000121000000bM1:<=R=/>J,HL1>=759?eW2X=?WLX@?X85P8DkW@XQ>W4XS9o"). Qed.
End CANSEC6.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC7. Context {rc : runConstT}.
Lemma rclean_magreeA : forall (P : Z -> Prop) m m' r, rclean m r -> magree bsegs P m m' ->
  (forall a, ATOP <= a < 2^47 -> P (shad a)) -> ATOP <= r_rlo r -> rclean m' r.
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_kit ()) ["CANSEC7"] "p'0h01Hh12Hsh24__x1h34__x2h44__x3h51zh61ah74__p1h84__p2h94__x4h:4__x5h;4__x6h<4__x7h=4__x8h>4__x9h?2Hah@7__arithhA4__ffhB8__varmaphC5__withD5__x10hE1shF2H0hG3H10hH3H11hI3H12hJ2H4hK2H7hL2H8hM2H9hN1qhO2q0hP2r0hQ2r1hR2H1hS3H13hT3H14hU3H15hV3H16hW3H17hX2H2hY2H3hZ4__p3h[4__p4h\5__x11h]5__x12h^5__x13h_5__x14h`5__x15ha2q1hb2r2hc2ABhd1Ehe3H18hf3H19hg3H20hh3H21hi3H22hj3H23hk3H24hl3H25hm3H26hn3H27ho3H28hp3H29hq3H30hr3H31hs3H32ht3H33hu3H34hv2H5hw2H6hx2HPhy2HShz2HUh{2LTh|2MGh}1Ph~2RLi002SRi011Ui022WRi032_Hi047__sat13i057__sat14i067__sat18i077__sat19i081mi092m'i0:2q2i0;2q3i0<2q4i0=1ri0>2r3i0?2r4i0@2r5p%0p%1p&0p;1p;2p;5p;4p;3p;6p;9p;7p;8g008Nj16Tg0093k107Tg009Qk10CTg00:4k10oTg02CHj2VTg02DCj14Tg02E<j18Tg02F5j10Tg02Foj11Tg02Gik508Tg00GMj2:Tg01jij4xTg016Ak10nTg00>@j1WTg00NBj1DTg00TEk20;Tg01fHj17Tg00E[j23Tg02Hek30:Tg02I`j4qTg0177j2CTg02J[j2gTg00GiR0j29Tg017Tj2KTg02KSj2UTg01>9j25Tg01h:k10PTg00@9k10gTg007nk10`Tg00SDk10_Tg00L3k10^Tg00LQk10\Tg00Sbk20KTg00Ngk20[Tg00HDk20ZTg00OIk20YTg00=fj3;Tg00P5k30XTg00PTk40WTg02L3j3bTg01=?j2PTg01=`j1`Tg01?6j2NTg01>Vj22Tg01?]j2OTg01@Dj2RTg01@jj2QTg022Fk20ITg022nk30HTg00F7j1ATg01APk10VTg01Ank20UTg023Rk20TTg024;j3|Tg01C8k20FTg01DMk205Tg00=Dk10DTg00M<k20ATg01F^j3yTg00Tbk30@Tg00E>j2FTg02L\k10QTg003Ok60LTg00<Uj1tTg02M`k60mTg02Nam90kTg00VEk401Tg02Obk40jTg00\@j4kTg00\kj7wTg001>k60hTg01BOk30fTg01H?k30<Tg01Cak20eTg00@Yk30aTg00KUk20bTg01E9k40cTg01EWk60dTg01F;k30MTg00M_k30NTg01LVk60]Tg00]Ok702Tg00^3j8vTg02PTk30iTf0R1#6#6p>03%D1#Dp>0Jf3R2f2R3'3f1R4/:1'9p=Bg00iaR5P3P4P1H0jp=h1941,93p>0Gg00m:R6/34g02QQR7,31'9p=_g00^WR81234;;6/91p=T1334/91p=a1241=;86p={1361p=H1317p>0Bg01;QS00/F1p==1:41,93p=m%D1#D#D#Dp=s%61#6#6#6p>0=%61#6#6#6#6#6#6#6p=X20K81p=jP3g00`;R7g00`ZR9P9g00a:R:P8P4g00_TR;P1Ckg00aZR<Fwp=uP8f4R=P2P3P4P1J0hp=iA;816p>00f5R>1523,K=1241'F5;8p=Y13631:41'9p=I1:341316'9p=S1541=;86p=MA;841p=~1234=;81p=Z20F81p=GB0f841p=^B0<841:0<83p=@g01IO-0e1p=pB0<841p=fg00lNR?@0a41p=o20b81p=LP8P3P4P1H0cp=?P3P7P9P9P:P8P4g01HhR@P1CkP<Fwp=JP4P7P9P9P:P1J0dp>0E20A81p=EB0M834>0N81p=\P3P7P9P9P:P8P4g00b:RAP1CkP<Fwp=eP4P7P9P9P:P1J0]p=dP3P7P9P9P:P4P1K02p=zB0N841p=cP=P7P9P9P:P2P7P9P9P:P8P3P;P4CkP<FwP1K02p=]P8P4P@P1Ckp>0SP8P4P;P1Ckp=nB0M841p>0RP=P7P9P9P:P2P7P9P9P:P3P<FwP4P1Gvp=lf6R;P7P9P9P:P>P=P2P7P9P9P:P3P4P1GvGvp>04P;P7P9P9P:P>P7P9P9P:P=P2P3GvP4P1Gvp=>1F419;83p=[%84/C1p=<Q00/F4/31p>0?1341,93p=}1534,K2/F19;8=p>0>P8P4PAP1Ckp>09P2P7P9P9P:P3P4P7P9P9P:P1P<FwK02p>061364/91p>0OB0i541p=rP>P7P9P9P:P=P2P3P7P9P9P:P4P1K02Gvp>0lp-0R7\8g00gHR<#6RA#6R@#6RB#6S01$03RC$07S02$0C&07B$0CS03$0oRD[S04Q04g02RF1V31P0P2%44RE%84RF%04%14I081:EFP5P>P=P2Cxp,2rcRF$0nREP1P1%WARG%DARH#DS05$0JS06#WRI+0;RJCBRKf8RL%74RMO1[^68%0=RN,3E1V;>[[[P1P>%42%82%02%12I08P0%4=RO%8=RP60:;POPPPN%1=RQCq%7NRN%7Q/CN5h;1gOP40G%4>%8>':P5f9RPPLf7ROCxf<RNPMO1\K^68%0LRQ,3Ef:RR/VP[[[[P1%4;%8;60:L%4ORS%8ORT%0ORU%1ORVCq%7URU%7V/CU5hP1gST40GP0%4LRT%8LRSPQ%1LRUCq%7QRQ%7U/CQ5hR1gTS'9%4P%8P':P5f=RSPNf;RTCxf@RQPMO1\K^68%0NRU,3Ef>RV/VS[[[[P1%4R%8R%0R%1RCq%0T#7RW%1T#7/CW5hS%4T%8T'g'9P0%7URU%1N#7/CU5hV%4N%8N'g%4S%8S':P5fARUPQf?RWCxfDRXPMO1\K^68%0Q,3EfBRY/VU[[[[P1%0V#7RZ%1V#7/CZ5hQ%4W%8W'g%4Q%8Q':P5PXfCRZPYCxfGR[PMO1\K^68%0Z,3EPP%4X%8X%0X%1XCqP0fERK#0RM%4K'3%8K%1KR\%WCR]1_M\9T\]5TM3afFS07,V[P1%0[%4['3fHRM#8%1MR\%0MR^1_^\9T\]7T]3aP0fIS08#8Q08#1R\'3Q08#0R^1_^\9T\]7T]fKR\fJS09'VP1%8\%1\'3fLS0:#0R^Q0:#1R_1_^_7T]7T]P0fMS0;#0R_/{]Q0;#1R^1__^7T]fOS0<fNS0='VP1Q0<#0/{]fPR^#1R_%0^/__7T]P0fQR_#1R^/{]%0_/_^fSS0>fRS0?'VP1Q0>#1/{]fTS0@#0Q0@#1'_P0fUS0A#0#HQ0A#1$0BfWS0BfVS0C'VP1Q0B#0#HfX#1$0BfZR^#0S0D#7S0EP1P1%1^S0F#7S0GCBS0H%WBR_Q00,C4'KR`#7f_RaP1O1XE8PMP`f[R`#0S0I%D<Rb#WRc'U%=1Rd/33S0Jf\Re#1Rf/UcRg#=7m3X58P1Q0I20;GcRh'5RiQ0I&0PFS0K%DbS0L#DS0M#D$0J#s#sRF#6#s#s#6$03$0=#X#X#W%DFS0N#s#s#6$03$0=#X#X#W,3E7aES0O&0g?RF&0`?S0P&0_8R?&0^8S0Q&0\8Rj20K86Rk%jc3u20[j:S0RP1P3g00baR:g00cARl+0Z20Y13=;:ldB0X864H0WS0SbAbBbC%HcP1b@b0Rl7bcDi%=iP4P4%1`S0T/Uc#=CBPgf]Rg#0Ri/5hS0U#=P2P2PdCBX58P115fhR:AbfclDi%0e/5h#=P3P3%=:CB1Pi_&00_R:#`Rff^Rm#0S0VP_Q0VP_Q0VP_EY[Q0V/N_1:6_Rn%0aRo/2_Rp?Ip_[1Oo_1:_6Rpf`Rq#0S0W/2_S0XQ0X5S_[Q0W/R_faS0Y#0S0Z/M_\:Q0Z/Q_fbS0[#0S0\/2_S0]Q0\'~\:Q0\/5_P8fcS0^#0S0_/2_P8fdS0`#1/P_feS0a#1RrP_PrP_PrP_EY\f1Nr_ffS0b#1S0c/2_Rr?Ir_\nQ0c/O_fgS0d#1S0e/2_S0fQ0f5S_\pQ0e/R_fhS0g#1S0h/M_\:Q0h/Q_fiS0i#1Rr/2_S0j/~r\:15r_P8fjS0k#1S0l/2_P8fkS0m#0/P]&00]Rs#`S0nflS0o#0RtP]PtP]PtP]EY[1Nt]1:6]S0pfmS0q#0Rt/2]Ru?Iu][1Ot]1:]6S0rfnS0s#0Rt/2]Ru=S]u[1Rt]foRt#0S0t/M]\sQ0t/Q]fpS0u#0Ru?Z]u\s15u]P8fqS0v#0/2]P8Q0KQ0O20IGI1:6GS0w%HI1:6J[[%HGRug00mXRvB0HGI4UW?%HJ\v^?ug00kKRI#AS0x#ARw#ARx#ARy#AS0y#ARz#AR{#AR|#AR}#GS0z&0V<-0U8R~%G|S0{'^20T8_R|%GyS0|5|8%GxRx20F8IS0}3@3@#p%A}R}#GS0~,^~%G{S10%GzS11%GwS12,^~'f3@Q0}9|8|S13%A}S14#GS15Q119|8|S16Q12Q0x#GS0x'f7@x3@#p+05/oF'oQ0P%LLS17??=?S18%LRS19??;?7?3%LPS1:??>?%LO7?2S1;7?4Q0QPjPj%j]S1<=Jjk-0EjS1=&0D9R9%EbR}Q1<%6H#ES1>%E@Rw3\5JjP9PjPj%j_Rz9ejkR{P9%D@#ES1?9ujkS1@1djNS1A5zjP9PjPjAJjzk-0EjR@P9%EHRHQ0L#ERIQ1?5\zS1B5JjP9PjPjP{P91djS%EBRB=ejzS1C5zjP9PjPjP@P9%6bS1D#ES1E=\zBS1F9Jj}P9PjPjPjQ0N#6$03$0=#X#WRB#jRbQ1E'cS0N%EARA1cbIS1G9ejAD]P9Pj%6C#X#X#X#X#X#WS1H#j9ujHS1IP9PjPj20SwkP9PjPj20A8<RC/n}P9PjPjPCAy8Ab-0RzRy%jGS1JQ06$0760@89ejyD]DlDlK04F>F>F>F>F>Q0RQ0SbAbBbCX28X38X48X98X:8X;8X<8X=8X>8XD8X77X87g01J;Ry\sS061K]R=[2=[%HRS1K/9N\nPy\:Ry1K_PS1L/FTS1M,~O[1:T_S1N,9W\n1K_R=[ON\y1FBRS1OP;P;1FBTCBQ1H,3R&00R13LRPP1CRB,K_S1PQ1PPJCB[[[[[[[[[^28^38^48^98^:8^;8^<8^=8^>8^D8^77^87P1%HYS1PQ1NP>PTPYPNPZfvS1N#1P=Q1N#0Q0:PEPRPQPUP[PMQ08Q0;Q0CQ0[OEb@c06c07bWbbbabVbUbTbSbIbQbObHbGbMbLbKbPbNbJbXbRbFb0PEQ00,C2,K_REPEPJCBeb1b1O2P4&0Q4DiW1XE8Q0HPmP4O1[^E8P`%4^RJ%8^REQ0DQ0FI081:JEB0:`JEPJPEQ0DQ0FCqS0FQ0EQ0GQ0E'CS0G5h`S0D1gJES0H'9S00'9PeP`PJPEQ0>%4`#7%W<R<,<`#7,317a1%4eRE/UcQ0J1<g<RJ/UcS0C#=,33S1Q'9X58P115EhS0JAbEclDiQ0J#=1<e</Uc#=,347a4Q0C%4mS0C/5h00?2S0J?}2dX58P115JhREAbJclDi%4gS1R/5hS1S00?3S1T%=E7}3Q0C/P_%4aREP_PEP_PEP_EY\f1NE_%4qS0C/2_RJ?IJ_\nQ0C/O_Q0Y#4S0C/2_RJ=S_J\pQ0C/R_Q0[#4RJ/M_\:1QJ_Q0^#4RJ?Z_J\:15J_P8Q0`#4/2_P8Q0a/<</P_Q0b/<<RJP_PJP_PJP_EY\f1NJ_Q0d/<<S0d/2_RJ?IJ_\nQ0d/O_Q0g/<<S0g/2_RJ=S_J\pQ0g/R_Q0i/<<RJ/M_\:1QJ_Q0k/<<RJ?Z_J\:15J_P8Q0m/<</2_P820IG]Q0w%H]20;G]RJ,:6[[B0HG]4VvX?u%HJ\v^?uQ0~Q0z,^~Q0y#G9|8|R|Q0|Q12Q13'f3@3@#pQ0{Q10Q16Q0xQ13'fRu7@x3@#p/oF'oQ0PQ18%L;7?3Q1;7?4Q0QPjPjP{P9Q1@1djT5zjP9PjPjP@P9%j<Rv9y8}Q1B5JjP9PjPjP{P9Q1AQ1C5zjP9PjPjP@P9Q1F9JjAP9PjPjPjQ0NPCQ1G9ujCD]P9PjQ1IP9PjPj1nkwP9PjPj1n}HP9PjPj1nwAP9PjPjPkPCQ1JQ0260@89ejCD]DlDlDlK04F>F>F>F>Q0RQ0SbAbBbCX28X38X48X98X:8X;8X<8X=8X>8X77X87%HPRG/9R\n1C=<1K_L;[R\yAmSR_\nQ1M,~>\y1FBPQ1O,3=7a=Q1H,3P13PT13TPAmGPJ[[\G[[[[[[^28^38^48^98^:8^;8^<8^=8^>8^77^87P1Q1K1:2_P2PRP=PT%1tQ0t%8t%4tRtPXPLPPPWPQPUQ07P[Q0>Q0BODb@c04c05bQbObIbHbGbMbLbPbNbKbJbYbFb0AI22Jeb1b1AI44JP\P3P1P2P3P8Q0U13d2RJ%1mRG/UcS0U#=7m2X58Q1R/Uc1<m<R6/UcS0B#=9}J2X58P4Q1SQ1R?bclDiQ1TQ1Q'9P815Gh15oh#=P=P=PdCBX58Q0B15Eh#=13=d7a=X58P1156hRhAb6clDiQ0J%=h7}21Po_Q0WP_Q0WP_Q0XI0>\fQ0W/N_Q0Z/2_Rh?Ih_\nQ0Z/O_Q0]Q0]5S_\pQ0\/R_Q0_/M_\:Q0_/Q_Q0`#0Rh?Z_h\:15h_P8Q0a#0/2_P8Q0c/P_Q0eP_Q0eP_Q0fI0>\fQ0e/N_Q0h/2_Rh?Ih_\nQ0h/O_Q0jQ0j5S_\p1Rr_Q0l/M_\:Q0l/Q_Q0m#1Rr?Z_r\:15r_P8Q0o#1/2_P8Q0q#4/P_Q0s#4RrP_PrP_PrP_EY\f1Nr_12t_Rr?Ir_\n1Ot_Q0u#4Rt/2_Rr=S_r\p1Rt_Q0v#4Rt/M_\:1Qt_frRt#4Rr?Z_r\:15r_P8fs#4/2_P8ft/<</P_fu/<<RrP_PrP_PrP_EY\f1Nr_Q1N/<<Rr/2_Rf?If_\n1Or_fw/<<Rr/2_Rf=S_f\p1Rr_fx/<<Rr/M_\:1Qr_fy/<<Rr?Z_r\:15r_P8fz/<</2_P8f{#1/P]Q0nf|#1RrP]PrP]PrP]EY[1Nr]Q0pf}#1Rr/2]R:?I:][1Or]Q0rf~#1Rr/2]R:=S]:[1Rr]p+01@#1Rr/M]\s1Qr]p+01A#1Rr?Z]r\s15r]P8p+01B#1/2]P8p+01C#0/P]Q0np+01D#0RrP]PrP]PrP]EY[1Nr]Q0pp+01E#0Rr/2]R:?I:][1Or]Q0rp+01F#0Rr/2]R:=S]:[1Rr]p+01G#0Rr/M]\s1Qr]p+01H#0Rr?Z]r\s15r]P8p+01I#0/2]P8Q14#A#ARr#ARs#GR:,^~Q0zQ0{1^~x'f3@%As#G%Gr,^~Q0|;@x7@:Q0xQ0}Q11Q12'f3@#p+05+05Q15Q0~Q10Q11,^~1f|u3@3@#p/oF'oQ0P%LW??W?%LT7?=Q1:%LS7?;7?3Q17%LN7?>Q19%LV7?O7?27?4Q0QPjPjQ1=P9Q1<Q01#EQ1?3\9JjIP9PjPjP{P9PjPjPkQ0M#ERT1djUD]P9PjPjP@P9Ay8HvQ05#ERv=\zT5JjP9PjPjP{P9Pj1djYPjQ0L#6#ERT009zH06P9PjPjP@P9Q1>=\zT9JjwP9PjPjP{P9Pj1djZPjQ1D#D#ERT009zH06P9PjPjP@P9A\z}T9JjIP9PjPjP{P9PjPjPkQ1D#6#ER{1djXD]P9PjPjP@P9Q1EA\zC{5JjP9PjPjPjQ1>,cbPA1cbv9ujAD]P9PjQ1?=JjkP9PjPj1nHIP9PjPjQ1E/nwP9PjPj1cbCPA1cb}9ejAD]DlDlK04F>F>F>F>F>F>F>F>F>Q0RQ0SbAbBbCX28X38X48X98X:8X;8X<8X=8X>8XD8X\8X]8X^8X_8X`8X77X87XZ7X[7Q061K]W=[OL[20OWU\n1CO<1K_N;[Q\yAmXQ_\n1K_S=[LU\yAm[U_\nQ1L=[SY\yQ1PQ09'9\nQ1L=[VZ\y1FBU1FBY,3R7aR&00U13WU13UW1FBSPVPV1FBWCB[[[[[[[[[[[[[^28^38^48^98^:8^;8^<8^=8^>8^D8^\8^]8^^8^_8^`8^77^87^Z7^[7P1Q0@/:_Q0;#HQ07#H1:W_PPPWQ07Q0;Q0@PQP[PLp+01KRL#1%0L%8L%4LQ0=PaQ0APVPXPKP\Q0:Q0?Q0>fYP^P`Q0bQ0sPtOPb@c0@c0<bubtbsbrbqc0?c0;bpbobnbmblc0>c0:bkbjbibhbgbbbabfbebWbVbUbQbObTbSbIbHbGbPbNbMbLbKbFb015o_#=P=P=%1a/5_#=CBeb1Q0UAbGclJ0Lb11UicAbiclJ0L%7iP3P3%1g#7CBeO2O3Pm%t3RmO1PaPmO15;D1ramQ03$0DRm5;D#`%t2Ri,ra=;Dm#`['9P0PaPiO1PqPiO15;D1rqi=;Dm#`%t=R=,rq=;Dm#`[PqP=O1Q0YP=O15;DP1Q0Y%t>R>O1Q0[P>O15;DQ0^%t;'r=;Dm#`Q0^%tO'r=;Dm#`[P4Y03WdP4P1O2n2001000000120000000b6c00W1XE8J0mQ0FQ00Q0<Q0DQ0HP5PgPeP`Q0EQ0GPMP\Q0I#7R\P1P1Q0T#7/C\,F\CBP3P4Q0KQ0OPFQ0P%L3%L27?4Q0QPjPjAujCARFPjAy8}C,cC-09AH06P9PjPFAejA}J0lQ0RQ0SbAbBbCX28X38X48P1P4P41C31,F1CBP4P3P3P2CB[^28^38^48P1%7GP2Q0V#7P3O4b@b0O2W?X68N90kQ09H01H01H01Q08H01byWwWvP4P1O2n2001000000121000000W0WJP4P1O2n2001000000121000000W0WYP4P1O2n2001000000121000000W0WXP4P1O2n2001000000121000000W0WRP4P1O2n2001000000121000000b0W~WxW|W{WcY02P4P1O2n2001000000121000000W0WzP4P1O2n2001000000121000000W0Y01P4P1O2n2001000000121000000W0P4P1O2n2001000000121000000W0Y0=Y09Y08W}o"). Qed.

(* [comment removed for export] *)
Lemma shad_not_in_blk : forall a X n, ATOP <= a < 2^47 -> ablk X (X + n) -> ~ (X <= shad a < X + n).
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_kit ()) ["CANSEC7"] "h02Hah12Hrh27__arithh34__ffh44__p1h54__p2h68__varmaph75__with84__x1h94__x2h:4__x3h;4__x4h<4__x5h=4__x6h>3ATRh?1Bh@2BBhA1HhB2H0hC2H1hD2H2hE2H3hF1XhG6__sat4hH6__sat5hI1ahJ1nhK1qhL1rhM1zp&0p;1p;2p;3p;4p;6p;7p;8g016Ak103Tg008Nj10Tg00>@j17Tg00NBj12Tg00TEj2UTg00GMj24Tg00E>j23Tg01o_j3dTg01fHj1bTg02SCj4_Tg00E[j29Tg0181j2STg01h:j1uTg02KSj2rTg01>9j2GTg00@9j1mTg007nj1lTg00SDj1kTg00L3j1iTg00LQj1hTg00Sbj2VTg00Ngj2cTg00HDj2aTg00OIj2`Tg00=fj3@Tg00P5j3^Tg00PTj4]Tg02L3j3\Tg001>j6[Tg01=?j2ZTg01=`j1YTg017Tj2XTg01>Vj2DTg01?6k202Tg01?]k201Tg00Gij2JTg01@Dk200Tg01@jj2~Tg022Fj2yTg022nj3xTg00F7j1<Tg023Rj2vTg024;j3OTg01Caj2RTg01APj1tTg01Anj2qTg01BOj3pTg01C8j2QTg01DMj2oTg00@Yj3PTg00KUj2MTg01E9j4LTg00=Dj1nTg00M<j2ATg00\@j4FTg01EWj6jTg01F;j3sTg00M_j3KTg01TTj7wTg0093j1gTg00Tbj3zTg00\kj7{Tg01H?j3fTg00]Oj7|Tg00^3j8}Tg01LVj6eTf0R0#2#2p=Nf2R1f1R2'9/J0p=:%00#0p=E%00#0#0#0#0#0#0#0p=;%20#2#2#2p=5%00#0#0#0p=Cg00^WR3/V0p=?P3P2g00_TP0CFp=>P2g00`;R4g00`ZR5P5g00a:R6P0g00aZF{p=1g00m:R7/90p=B1420,J1p=W1Q30p==Af320p=6P3P2g00b:P0CFp=IP1P4P5P5P6P2P0F|p=Hf3R8P4P5P5P6P1P2P0G}p=8P2P4P5P5P6P0Eep=Tp,2rcR9$03R:g00gHR;#0R<#7R=%2<R>#2#NR?#7R@'URA,417:113129d91f4RB#bRC1381,4C5:8RCP9PB13B8RDP2C_g02TB,9D%0<RD#0RE#E#;#5#5#5#5#0#E#C#;#7RF/9B'S%u9%2;R9#2#5#5#5RG#0#2#NRH#2#5#0#E#C#;#;#7RI%2GRG#5#5#0#E#C#;#;#7,9:RJ7::P3f7RK%79RL'r%0G#E#C#;#7RG/30RMf6RN,3K,4M5:KXM3P11U=L,GKRMg00lNRO#mRP%lORQ%k3RR%i3RS%h3RT1V37RU%?L'>'11cT6RVP0P1g00baRWg00cARX'a1`01=@WXdA^372C]RXb3b6b7%BLP0b29\KLE[13GMRMf5RL,3N,4M5:Nf8RM%7ERE'ZA@3E7RW#Yf9RY1GYE,XE1DYE'35@3[202YE147ERZf:R[/DER\#B?W\E[201[E14E7f;R\/DER],4E19]7'J[200\Ef<R]/GE=@37\W1~]Ef=R^/DE=@3^\W1G^EP3f>/DEP31y=@147=%B@147A[[%B=R7g00mXR_Ax=@2UW0%BA\_^07p-0R7g00kKR_#<R@#<R`#<#<Ra#<Rb#<Rc#<Rd#=%=cRc%=bRb1v3ERe%=aRa5O3%=`9O3e%=@'6'6'6'6'6g01IOR@'R%<d#=%t;,q3=p3c1Q3_R_'6'616ba,6_/R@'o=POP5POPQP3P31M3BP11M3NCLP2P31M3LP8PRCLCLPSPTPT%?ERS,IU,1T%n5RR%09,A3R2,>U,1T1I2S,1T5HTC8PRPTPTPTP4P5P5P6P3PSg01HhRQPUCF,1TEjPRP31A3<R<PQ1A3DRD9s3S=K32CF,1TC8PRPT%?I1A3;R;'>,1T1TTM5HTPRPTPTP4P5P5P61A39R91A3>5K3R>%CH#;#7RH#?'>,1T%?F/>9,1TFwPRPT%?G=K3DRD,>9,1T1ID>,1T5HTPRPT1>;<,1T%?=%g?5z3,I<,1T5HTPR1TTYC8C8C8C8C8C8PVPXb3b6b7X83X93X:3X;3X<3X=3X47W5%BN?WNE\Zg01J;RZ\W1XEL/3K9@38[A:I1M13LK/9H19FL'S13GKRG13NM,4G5:N14NA9:LNP^[[[[[[^83^93^:3^;3^<3^=3^47^57P0PZPJP8f@PBfAfBP:PMPYP\P]P[f?O>b2bGbHbLbKbEbDbCbBbAb1PZeb>b@W1%YCeW?W0XJ3XF3XI3o"). Qed.

(* [comment removed for export] *)
Lemma shad_stack_client : forall CI LB SP a, ATOP <= a < 2^47 -> aclient_addr CI LB SP (shad a).
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_kit ()) ["CANSEC7"] "h02CIh12Hah22LBh32SPh41ap;2p;1p;3p;6g0126j2>Tg007nj15Tg016Aj18Tg00E[j24Tg008Nj1=Tg00>@j13Tg00NBj10Tg00TEj27Tg00GMj21Tg00Gij22Tg01g@j26Tg01j1j29Tg0181j2:Tg01;7j3<Tg02U6j6;Tg00^WR0/>0#5g00fO#5p,2rcR1#8R2f0R3'4g00gH#=R4#3%04#0#0#0#3'7R4,13'2P1f4R1f3R5f2f1R614261164'216161956':;<3E;W1X40X30W2W0o"). Qed.
End CANSEC7.

