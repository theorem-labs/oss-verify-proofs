(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv BzTac.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Definition SAVES (s4 s3 s2 s1 s0 ra0 : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition atEnd (raE : Z) (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
  MS (mkR (Z_to_bv 64 raE) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0 s1
          (Z_to_bv 64 (bv_unsigned sp + -128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 0x15d70) fc None m (seg_rom s0segs).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma glueD4 : forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : bzs) (dl dn : Z) (Q : machine_state -> Prop),
  rw_cells s0segs m (bv_unsigned sp + -128) (STRM_CELLS b) -> bzs_wf b -> mem_inv s0segs m ->
  rw_cells s0segs m dl [C4 (Z_to_bv 64 dn)] -> dn = bs_dlen b -> (bv_unsigned sp <= dl)%Z -> (dl + 4 <= 2 ^ 64)%Z ->
  (forall t0' a1' m', rw_cells s0segs m' dl [C4 (Z_to_bv 64 (dn - bs_av b))] ->
     rw_cells s0segs m' (bv_unsigned sp + -128) (STRM_CELLS b) ->
     munch [(dl, dl + 4)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
     evt s0segs Q (atEnd 0x1600c sp gp tp t0' t1 t2 (Z_to_bv 64 dl) (Z_to_bv 64 4) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m')) ->
  evt s0segs Q (MS (mkR (Z_to_bv 64 0x15fe4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 dl) s1
                      (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x15fe4) fc None m (seg_rom s0segs)).
Proof.
  intros until Q. intros STRM BWF MI DL DN DLLO DLHI HK. pose_word_ranges.
  cps_destruct BWF as (Q1 & Q2 & AI & AV & LEN & DLEN).
  pose proof (munch_refl [(dl, dl + 4)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
  (* [comment removed for export] *)
  step. bnt. step. step. step. bnt.
  wstep. wstep. wstep. lstep. step. step.
  enter_with HK; [ st_eq | exact DL | exact STRM | exact MU | exact WM | exact MI ].
Qed.

(* [comment removed for export] *)
Lemma glueDx : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rc : Z) (Q : machine_state -> Prop),
  mem_inv s0segs m -> (rc mod 2 ^ 64 <> 0)%Z -> (rc mod 2 ^ 64 <> 4)%Z ->
  (forall a0', evt s0segs Q (atEnd 0x16034 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 rc) a0' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)) ->
  evt s0segs Q (MS (mkR (Z_to_bv 64 0x15fe4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0 s1
                      (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x15fe4) fc None m (seg_rom s0segs)).
Proof.
  intros until Q. intros MI R0 R4 HK. pose_word_ranges.
  (* [comment removed for export] *)
  step. bnt. step. step. step. btk. step. step.
  enter_with HK. st_eq.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition inEnd (pc : Z) (raE : Z) (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (S : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
  MS (mkR (Z_to_bv 64 raE) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -128)) (Z_to_bv 64 (S + 2047))
          a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom s0segs).

(* [comment removed for export] *)
Lemma glueE1 : forall (raE : Z) (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : bzs) (h : dsh) (d : dsm) (S lo : Z) (Q : machine_state -> Prop),
  rw_cells s0segs m (bv_unsigned sp + -128) (STRM_CELLS b) -> bs_S b = S ->
  rw_cells s0segs m S (HEAD_CELLS h) -> sh_strm h = (bv_unsigned sp - 128)%Z ->
  rw_cells s0segs m (S + 3152) (MID_CELLS d) ->
  (0 < S)%Z -> (S + 64144 <= lo)%Z -> (S mod 8 = 0)%Z -> ((bv_unsigned sp - 128) mod 8 = 0)%Z ->
  stk s0segs m lo (bv_unsigned sp + -128) -> (0x66000 <= lo)%Z -> (lo <= bv_unsigned sp - 160)%Z -> mem_inv s0segs m ->
  (0 <= raE < 2 ^ 64)%Z ->
  (forall (a0' a2' : word) (m' : word -> option byte) (j8 : list byte),
     rw_cells s0segs m' (bv_unsigned sp + -160) [CB 8 j8; C8 s1; C8 s0; C8 (Z_to_bv 64 raE)] ->
     rw_cells s0segs m' (bv_unsigned sp + -128) (STRM_CELLS b) ->
     rw_cells s0segs m' S (HEAD_CELLS h) -> rw_cells s0segs m' (S + 3152) (MID_CELLS d) ->
     stk s0segs m' lo (bv_unsigned sp + -160) ->
     munch [(bv_unsigned sp + -160, bv_unsigned sp + -128)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
     evt s0segs Q (inEnd 0x15db4 raE sp gp tp t0 t1 t2 a0' (Z_to_bv 64 (sm_tt d)) a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m')) ->
  evt s0segs Q (MS (mkR (Z_to_bv 64 raE) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0 s1
                      (Z_to_bv 64 (bv_unsigned sp + -128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x15d70) fc None m (seg_rom s0segs)).
Proof.
  intros until Q. intros STRM BS HD HS MIDc S0 SHI SA8 SP8 ST LOLO LO MI RA HK. pose_word_ranges.
  pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -128)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
  carve_frame 32%nat ST.
  (* [comment removed for export] *)
  do 4 lstep. step. step. step. bnt. step. step. notrap.
  (* [comment removed for export] *)
  step. rewrite BS. step. bnt. step. step. notrap. step. rewrite HS. step. bnt. step. step.
  enter_with HK; [ st_eq | exact FR | exact STRM | exact HD | exact MIDc | exact ST | exact MU | exact WM | exact MI ].
Qed.

(* [comment removed for export] *)
Lemma glueE_free : forall (site next : Z) (raE : Z) (sp gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : bzs) (S p : Z) (Q : machine_state -> Prop),
  ((site = 0x15db4 /\ next = 0x15dc4) \/ (site = 0x15dc8 /\ next = 0x15dd8) \/ (site = 0x15ddc /\ next = 0x15dec))%Z ->
  rw_cells s0segs m (bv_unsigned sp + -128) (STRM_CELLS b) ->
  bs_bzfree b = Z_to_bv 64 0x13e3c -> bs_opaque b = Z_to_bv 64 0 ->
  (0 < p < 2 ^ 64)%Z -> mem_inv s0segs m ->
  (forall a2', evt s0segs Q (inEnd 0x293c4 next sp gp tp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 p) a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m)) ->
  evt s0segs Q (inEnd site raE sp gp tp t0 t1 t2 a0 (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m).
Proof.
  intros until Q. intros SITE STRM BF BO P MI HK. pose_word_ranges. unfold inEnd.
  destruct SITE as [[-> ->] | [[-> ->] | [-> ->]]].
  all: step; bnt; step; rewrite BF; step; rewrite BO; step.
  all: step; bnt; step; step.
  all: enter_with HK; st_eq.
Qed.

(* [comment removed for export] *)
Lemma glueE_skip : forall (site next : Z) (raE : Z) (sp gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (Q : machine_state -> Prop),
  ((site = 0x15db4 /\ next = 0x15dc4) \/ (site = 0x15dc8 /\ next = 0x15dd8) \/ (site = 0x15ddc /\ next = 0x15dec))%Z ->
  mem_inv s0segs m ->
  evt s0segs Q (inEnd next raE sp gp tp t0 t1 t2 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m) ->
  evt s0segs Q (inEnd site raE sp gp tp t0 t1 t2 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m).
Proof.
  intros until Q. intros SITE MI HK. unfold inEnd in *.
  destruct SITE as [[-> ->] | [[-> ->] | [-> ->]]]; step; btk; exact HK.
Qed.

(* [comment removed for export] *)
Lemma glueE_load : forall (site : Z) (raE : Z) (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d : dsm) (S : Z) (Q : machine_state -> Prop),
  (site = 0x15dc4 \/ site = 0x15dd8)%Z ->
  rw_cells s0segs m (S + 3152) (MID_CELLS d) -> (0 < S)%Z -> (S + 64144 < 2 ^ 64)%Z -> mem_inv s0segs m ->
  evt s0segs Q (inEnd (site + 4)%Z raE sp gp tp t0 t1 t2 a0 (Z_to_bv 64 (if (site =? 0x15dc4)%Z then sm_ll16 d else sm_ll4 d)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m) ->
  evt s0segs Q (inEnd site raE sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m).
Proof.
  intros until Q. intros SITE MIDc S0 SHI MI HK. unfold inEnd in *. pose_word_ranges.
  destruct SITE as [-> | ->]; cbn [Z.eqb Pos.eqb] in HK; step; exact HK.
Qed.

(* [comment removed for export] *)
Lemma glueE5 : forall (raE : Z) (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : bzs) (S : Z) (Q : machine_state -> Prop),
  rw_cells s0segs m (bv_unsigned sp + -128) (STRM_CELLS b) -> bs_S b = S ->
  bs_bzfree b = Z_to_bv 64 0x13e3c -> bs_opaque b = Z_to_bv 64 0 ->
  (0 < S < 2 ^ 64)%Z -> mem_inv s0segs m ->
  (forall a2', evt s0segs Q (inEnd 0x293c4 0x15dfc sp gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 S) a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m)) ->
  evt s0segs Q (inEnd 0x15dec raE sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m).
Proof.
  intros until Q. intros STRM BS BF BO S0 MI HK. pose_word_ranges. unfold inEnd in *.
  step. rewrite BS. step. rewrite BF. step. rewrite BO. step.
  step. bnt. step. step.
  enter_with HK. st_eq.
Qed.

(* [comment removed for export] *)
Lemma glueE6 : forall (raE : Z) (raX sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (xs0 xs1 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : bzs) (S lo : Z) (j8 : list byte) (Q : machine_state -> Prop),
  rw_cells s0segs m (bv_unsigned sp + -128) (STRM_CELLS b) ->
  rw_cells s0segs m (bv_unsigned sp + -160) [CB 8 j8; C8 xs1; C8 xs0; C8 (Z_to_bv 64 raE)] ->
  stk s0segs m lo (bv_unsigned sp + -160) -> (0x66000 <= lo)%Z -> (lo <= bv_unsigned sp - 160)%Z -> mem_inv s0segs m ->
  (0 <= raE < 2 ^ 64)%Z -> (raE mod 2 = 0)%Z ->
  (forall m', rw_cells s0segs m' (bv_unsigned sp + -128)
                 (STRM_CELLS (BZS (bs_src b) (bs_len b) (bs_ai b) (bs_til b) (bs_tih b) (bs_q1 b) (bs_dst b) (bs_dlen b) (bs_av b)
                                  (bs_tol b) (bs_toh b) (bs_q2 b) 0 (bs_bzalloc b) (bs_bzfree b) (bs_opaque b))) ->
     stk s0segs m' lo (bv_unsigned sp + -128) ->
     munch [(bv_unsigned sp + -160, bv_unsigned sp + -128); (bv_unsigned sp + -80, bv_unsigned sp + -72)]%Z m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
     evt s0segs Q (MS (mkR (Z_to_bv 64 raE) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 xs0 xs1
                          (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 raE) fc None m' (seg_rom s0segs))) ->
  evt s0segs Q (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -128)) (Z_to_bv 64 (S + 2047))
                       a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15dfc) fc None m (seg_rom s0segs)).
Proof.
  intros until Q. intros STRM FRE ST LOLO LO MI RA RA2 HK. pose_word_ranges. unfold inEnd in *.
  pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -128); (bv_unsigned sp + -80, bv_unsigned sp + -72)]%Z m) as MU.
  pose proof (wmono_refl s0segs m) as WM.
  (* [comment removed for export] *)
  step. lstep. step. step. step. step.
  release_frame FRE ST (bv_unsigned sp + -128)%Z.
  step. rewrite (ret_pc_lit raE) by lia.
  enter_with HK; [ st_eq | exact STRM | exact ST | exact MU | exact WM | exact MI ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
