(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortM CmpMem BzCLemmasMs CmpMsKit AsanKit AsanCut AsanCutB0.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition amenv_shf (Y : amenv) (SHF : Z) : Prop := sanchor (am_FB Y) SHF /\ SH_LO <= SHF /\ SHF + 652 <= SH_HI.

(* [comment removed for export] *)
Definition amenv_offsh (X : msenv) (Y : amenv) : Prop :=
  (me_A1 X + ARR1_SIZE <= SH_LO \/ SH_HI <= me_A1 X) /\ (me_A2 X + ARR2_SIZE <= SH_LO \/ SH_HI <= me_A2 X) /\
  (me_FT X + 262148 <= SH_LO \/ SH_HI <= me_FT X) /\ (am_FB Y + 5216 <= SH_LO \/ SH_HI <= am_FB Y).

(* [comment removed for export] *)
Definition amenv_shx (X : msenv) (Y : amenv) (SHF : Z) : Prop :=
  (apartm (me_A1 X) ARR1_SIZE SHF 652 /\ apartm (me_A2 X) ARR2_SIZE SHF 652 /\ apartm (me_FT X) 262148 SHF 652) /\
  (apartm (am_SLO Y) 400 SHF 652 /\ apartm (am_SHI Y) 400 SHF 652 /\ apartm (am_SD Y) 400 SHF 652 /\
   apartm (am_RO Y) 1024 SHF 652 /\ apartm (am_BD Y) 256 SHF 652 /\ apartm (am_CS Y) 1024 SHF 652 /\ apartm (am_CE Y) 1024 SHF 652) /\
  SHF + 652 <= am_P Y - 32 /\ SH_HI <= am_P Y - 32 /\ SHF + 652 <= me_lo X /\ SH_HI <= me_lo X.

(* [comment removed for export] *)

Lemma amsh_1 : forall X Y SHF, amenv_shx X Y SHF -> me_A1 X + ARR1_SIZE <= SHF \/ SHF + 652 <= me_A1 X.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_2 : forall X Y SHF, amenv_shx X Y SHF -> me_A2 X + ARR2_SIZE <= SHF \/ SHF + 652 <= me_A2 X.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_F : forall X Y SHF, amenv_shx X Y SHF -> me_FT X + 262148 <= SHF \/ SHF + 652 <= me_FT X.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_SLO : forall X Y SHF, amenv_shx X Y SHF -> am_SLO Y + 400 <= SHF \/ SHF + 652 <= am_SLO Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_SHI : forall X Y SHF, amenv_shx X Y SHF -> am_SHI Y + 400 <= SHF \/ SHF + 652 <= am_SHI Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_SD : forall X Y SHF, amenv_shx X Y SHF -> am_SD Y + 400 <= SHF \/ SHF + 652 <= am_SD Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_RO : forall X Y SHF, amenv_shx X Y SHF -> am_RO Y + 1024 <= SHF \/ SHF + 652 <= am_RO Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_BD : forall X Y SHF, amenv_shx X Y SHF -> am_BD Y + 256 <= SHF \/ SHF + 652 <= am_BD Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_CS : forall X Y SHF, amenv_shx X Y SHF -> am_CS Y + 1024 <= SHF \/ SHF + 652 <= am_CS Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_CE : forall X Y SHF, amenv_shx X Y SHF -> am_CE Y + 1024 <= SHF \/ SHF + 652 <= am_CE Y.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). assumption. Qed.
Lemma amsh_P : forall X Y SHF, amenv_shx X Y SHF -> SHF + 652 <= am_P Y - 32 /\ SH_HI <= am_P Y - 32.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). split; assumption. Qed.
Lemma amsh_L : forall X Y SHF, amenv_shx X Y SHF -> SHF + 652 <= me_lo X /\ SH_HI <= me_lo X.
Proof. intros X Y SHF ((?&?&?)&(?&?&?&?&?&?&?)&?&?&?&?). split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record slv := mkSLV { v80 : word; v88 : word; v96 : word; v104 : word; v112 : word; v120 : word; v128 : word;
                      v144 : word; v152 : word; v160 : word; v168 : word; v176 : word; v184 : word;
                      v216 : word; v224 : word; v232 : word; v240 : word; v248 : word; v256 : word; v264 : word; v272 : word;
                      v312 : word; v328 : word; v336 : word; v344 : word; v352 : word; v360 : word; v368 : word; v376 : word; v384 : word; v392 : word;
                      v408 : word; v416 : word; v440 : word; v480 : word }.
Definition slb_cells (X : msenv) (Y : amenv) (SHF SHn : Z) (s : slv) : list cell :=
  [C8 (Z_to_bv 64 (me_n X * budget_q)); C8 (Z_to_bv 64 (SHF + 506)); C8 (Z_to_bv 64 (SHF + 362)); C8 (Z_to_bv 64 SHn); C8 (Z_to_bv 64 (me_E X + 108));   (* [comment removed for export] *)
   C8 (Z_to_bv 64 (SHF + 178)); C8 (Z_to_bv 64 (me_E X)); C8 (Z_to_bv 64 (am_FB Y)); C8 (Z_to_bv 64 (am_FB Y)); C8 (Z_to_bv 64 (me_n X - 1));            (* [comment removed for export] *)
   C8 (v80 s); C8 (v88 s); C8 (v96 s); C8 (v104 s); C8 (v112 s); C8 (v120 s); C8 (v128 s);                                                               (* [comment removed for export] *)
   C8 (Z_to_bv 64 0);                                                                                                                                     (* [comment removed for export] *)
   C8 (v144 s); C8 (v152 s); C8 (v160 s); C8 (v168 s); C8 (v176 s); C8 (v184 s);                                                                          (* [comment removed for export] *)
   C8 (Z_to_bv 64 (am_CE Y)); C8 (Z_to_bv 64 (am_CS Y)); C8 (Z_to_bv 64 SHF);                                                                             (* [comment removed for export] *)
   C8 (v216 s); C8 (v224 s); C8 (v232 s); C8 (v240 s); C8 (v248 s); C8 (v256 s); C8 (v264 s); C8 (v272 s);                                                (* [comment removed for export] *)
   C8 (Z_to_bv 64 (am_BD Y)); C8 (Z_to_bv 64 (am_SD Y)); C8 (Z_to_bv 64 (am_SHI Y)); C8 (Z_to_bv 64 (am_SLO Y));                                          (* [comment removed for export] *)
   C8 (v312 s);                                                                                                                                           (* [comment removed for export] *)
   C8 (Z_to_bv 64 (18446744073709551615 - me_A2 X));                                                                                                      (* [comment removed for export] *)
   C8 (v328 s); C8 (v336 s); C8 (v344 s); C8 (v352 s); C8 (v360 s); C8 (v368 s); C8 (v376 s); C8 (v384 s); C8 (v392 s);                                   (* [comment removed for export] *)
   C8 (Z_to_bv 64 (me_n X));                                                                                                                              (* [comment removed for export] *)
   C8 (v408 s); C8 (v416 s);                                                                                                                              (* [comment removed for export] *)
   C8 (Z_to_bv 64 (am_RO Y)); C8 (Z_to_bv 64 (me_FT X));                                                                                                  (* [comment removed for export] *)
   C8 (v440 s);                                                                                                                                           (* [comment removed for export] *)
   C8 (Z_to_bv 64 (me_A2 X + me_qo X)); C8 (Z_to_bv 64 (me_A2 X)); C8 (Z_to_bv 64 (me_A1 X)); C8 (Z_to_bv 64 (18446744073709551615 - me_FT X));           (* [comment removed for export] *)
   C8 (v480 s); C8 (Z_to_bv 64 (am_FB Y))].                                                                                                               (* [comment removed for export] *)
Lemma slb_cells_size : forall X Y SHF SHn s, cells_size (slb_cells X Y SHF SHn s) = 496%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record slq := mkSLQ { q80 : word; q88 : word; q96 : word; q104 : word; q160 : word; q168 : word; q176 : word; q184 : word; q224 : word; q232 : word;
                      q240 : word; q248 : word; q264 : word; q272 : word; q312 : word; q328 : word; q336 : word; q344 : word; q352 : word; q392 : word;
                      q408 : word; q416 : word; q440 : word; q480 : word }.
Definition slq_slv (Y : amenv) (q : slq) : slv :=
  mkSLV (q80 q) (q88 q) (q96 q) (q104 q) (Z_to_bv 64 65535) (Z_to_bv 64 18446744073707454463) (Z_to_bv 64 (18446744073709551615 - am_BD Y))
        (Z_to_bv 64 (18446744073709551615 - am_CE Y)) (Z_to_bv 64 (18446744073709551615 - am_CS Y)) (q160 q) (q168 q) (q176 q) (q184 q)
        (Z_to_bv 64 0) (q224 q) (q232 q) (q240 q) (q248 q) (Z_to_bv 64 (18446744073709551615 - am_SLO Y)) (q264 q) (q272 q)
        (q312 q) (q328 q) (q336 q) (q344 q) (q352 q) (Z_to_bv 64 (18446744073709551615 - am_SD Y)) (Z_to_bv 64 (18446744073709551615 - am_SHI Y))
        (Z_to_bv 64 2147483647) (Z_to_bv 64 0) (q392 q)
        (q408 q) (q416 q) (q440 q) (q480 q).
Definition slm_cells (X : msenv) (Y : amenv) (SHF SHn : Z) (q : slq) : list cell := slb_cells X Y SHF SHn (slq_slv Y q).

(* [comment removed for export] *)
Record nxt := mkNXT { n0 : word; n1 : word; n2 : word; n3 : word; n4 : word; n5 : word; n6 : word; n7 : word; n8 : word }.
Definition nxt_cells (x : nxt) : list cell := [C4 (n0 x); C4 (n1 x); C4 (n2 x); C4 (n3 x); C4 (n4 x); C4 (n5 x); C4 (n6 x); C4 (n7 x); C4 (n8 x)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.

(* [comment removed for export] *)
Ltac amenv_shx_open X Y SHF SHX :=
  pose proof (amsh_1 X Y SHF SHX) as ZS1; pose proof (amsh_2 X Y SHF SHX) as ZS2; pose proof (amsh_F X Y SHF SHX) as ZSF;
  pose proof (amsh_SLO X Y SHF SHX) as ZSLO; pose proof (amsh_SHI X Y SHF SHX) as ZSHI; pose proof (amsh_SD X Y SHF SHX) as ZSD;
  pose proof (amsh_RO X Y SHF SHX) as ZSRO; pose proof (amsh_BD X Y SHF SHX) as ZSBD; pose proof (amsh_CS X Y SHF SHX) as ZSCS;
  pose proof (amsh_CE X Y SHF SHX) as ZSCE;
  let H := fresh "ZSPH" in pose proof (amsh_P X Y SHF SHX) as H; destruct H as [ZSP ZSH]; unfold SH_HI in ZSH;
  let H2 := fresh "ZSPL" in pose proof (amsh_L X Y SHF SHX) as H2; destruct H2 as [ZSL ZSLH]; unfold SH_HI in ZSLH;
  box_ors.

(* [comment removed for export] *)
Ltac open_slb_in H := unfold slm_cells, slq_slv, slb_cells in H;
  cbn [v80 v88 v96 v104 v112 v120 v128 v144 v152 v160 v168 v176 v184 v216 v224 v232 v240 v248 v256 v264 v272 v312 v328 v336 v344 v352 v360 v368 v376 v384 v392 v408 v416 v440 v480
       q80 q88 q96 q104 q160 q168 q176 q184 q224 q232 q240 q248 q264 q272 q312 q328 q336 q344 q352 q392 q408 q416 q440 q480] in H.
Ltac open_nx_in H := unfold nxt_cells in H; cbn [n0 n1 n2 n3 n4 n5 n6 n7 n8] in H.
(* [comment removed for export] *)
(* [comment removed for export] *)
