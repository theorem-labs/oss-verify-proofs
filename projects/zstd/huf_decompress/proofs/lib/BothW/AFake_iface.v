(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (20 recorded proofs replaced by written proofs (fk_fsize_pos, fk_nframes_pos, fk_class_bytes and 17 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ALayout FsKit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFake_iface () := "C47Corelib4Init5Logic7eq_rectC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegc59OSSVerify5KrLib5BothW;AFake_iface8fk_fsizeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib5BothW;AFake_iface:fk_nframesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z:pow_succ_rC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdc59OSSVerify5KrLib5BothW;AFake_iface8fk_flagsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_iface9fk_framesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divc59OSSVerify5KrLib5BothW;AFake_iface<fk_fsize_posC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_mulC35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib5BothW;AFake_iface8fk_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_iface5fflagC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_iface7fk_flagC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c59OSSVerify5KrLib5BothW;AFake_iface<fk_flags_offC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_iface7FK_NCLSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_iface>fk_class_bytesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03c59OSSVerify5KrLib5BothW;AFake_iface6FAKESZC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init5Logic3notc59OSSVerify5KrLib5BothW;AFake_iface>fk_frame_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00K47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_iface9afake_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indK47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame@disjoint_outsideC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2Inc59OSSVerify5KrLib5BothW;AFake_iface5AFAKEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_iface:afake_geomC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_iface;afake_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_iface?afake_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8ablk_linC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;Forall_implc59OSSVerify5KrLib5BothW;AFake_ifaceDdisjoint_from_ForallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5FsKit5dc_atC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5FsKitAdisjoint_from_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5FsKit:dc_at_any2C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5BothW5FsKit9dc_at_anyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c59OSSVerify5KrLib5BothW;AFake_iface=fk_flag_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_ifaceCmunch_outside_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1K59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5BothW;AFake_iface<afake_blocksC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6abkind00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z7add_modc59OSSVerify5KrLib5BothW;AFake_iface=fk_frame_al64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_iface;fflag_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8ablk_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_ifaceBfk_frames_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;AFake_iface8afake_lbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5FsKit8dc_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5FsKit8c1_of_dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init5Logic2or01c59OSSVerify5KrLib5BothW;AFake_iface:afake_flagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z8leb_reflC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z8sub_diagC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib3MemAwrite_to_mem_specC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz01c59OSSVerify5KrLib5BothW;AFake_ifaceAfk_flags_disjointC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition FAKESZ : Z := 11571200.                 (* [comment removed for export] *)
Definition FK_NCLS : Z := 11.                      (* [comment removed for export] *)
Definition fk_nframes (c : Z) : Z := 2 ^ (14 - c). (* [comment removed for export] *)
Definition fk_fsize (c : Z) : Z := 2 ^ (6 + c).    (* [comment removed for export] *)
Definition fk_flags (L : alayout) (c : Z) : Z := al_fake L + 4096 + (32768 - 2 ^ (15 - c)).
Definition fk_frames (L : alayout) (c : Z) : Z := al_fake L + 36864 + c * 1048576.
Definition fk_flag (L : alayout) (c pos : Z) : Z := fk_flags L c + pos.
Definition fk_frame (L : alayout) (c pos : Z) : Z := fk_frames L c + pos * fk_fsize c.
(* [comment removed for export] *)
Definition fflag (L : alayout) (c F : Z) : Z := fk_flags L c + (F - fk_frames L c) / fk_fsize c.
(* [comment removed for export] *)
Definition fk_hint (L : alayout) (c : Z) : Z := al_fake L + 8 * c.

Lemma fk_fsize_pos : forall c, 0 <= c -> 0 < fk_fsize c.
Proof. intros c Hc. unfold fk_fsize. apply Z.pow_pos_nonneg; lia. Qed.
Lemma fk_nframes_pos : forall c, c <= 14 -> 0 < fk_nframes c.
Proof. intros c Hc. unfold fk_nframes. apply Z.pow_pos_nonneg; lia. Qed.
Lemma fk_class_bytes : forall c, 0 <= c <= 14 -> fk_nframes c * fk_fsize c = 1048576.
Proof.
  intros c Hc. unfold fk_nframes, fk_fsize. rewrite <- Z.pow_add_r by lia.
  replace (14 - c + (6 + c)) with 20 by lia. reflexivity.
Qed.
Lemma fk_flags_off : forall c, 0 <= c <= 14 -> 0 <= 32768 - 2 ^ (15 - c) /\ 32768 - 2 ^ (15 - c) + 2 ^ (14 - c) <= 32768 - 2 ^ (14 - c).
Proof.
  intros c Hc. assert (E : 2 ^ (15 - c) = 2 * 2 ^ (14 - c)).
  { replace (15 - c) with (Z.succ (14 - c)) by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
  rewrite E. assert (0 < 2 ^ (14 - c)) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ (14 - c) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2^14) with 16384 in *. lia.
Qed.
Lemma fflag_frame : forall L c pos, 0 <= c -> fflag L c (fk_frame L c pos) = fk_flag L c pos.
Proof.
  intros L c pos Hc. unfold fflag, fk_frame, fk_flag. f_equal.
  pose proof (fk_fsize_pos c Hc). replace (fk_frames L c + pos * fk_fsize c - fk_frames L c) with (pos * fk_fsize c) by lia.
  apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma fk_flag_range : forall L c pos, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
  al_fake L + 4096 <= fk_flag L c pos < al_fake L + 36864.
Proof.
  intros L c pos Hc Hp. unfold fk_flag, fk_flags, FK_NCLS, fk_nframes in *.
  pose proof (fk_flags_off c ltac:(lia)). lia.
Qed.
Lemma fk_frame_range : forall L c pos, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
  fk_frames L c <= fk_frame L c pos /\ fk_frame L c pos + fk_fsize c <= fk_frames L c + 1048576
  /\ al_fake L + 36864 <= fk_frame L c pos /\ fk_frame L c pos + fk_fsize c <= al_fake L + FAKESZ.
Proof.
  intros L c pos Hc Hp. unfold fk_frame, fk_frames, FK_NCLS, FAKESZ in *.
  pose proof (fk_class_bytes c ltac:(lia)) as CB. pose proof (fk_fsize_pos c ltac:(lia)).
  assert (pos * fk_fsize c + fk_fsize c <= 1048576) by nia. nia.
Qed.
(* [comment removed for export] *)
Lemma fk_frames_disjoint : forall L c1 p1 c2 p2,
  0 <= c1 < FK_NCLS -> 0 <= p1 < fk_nframes c1 -> 0 <= c2 < FK_NCLS -> 0 <= p2 < fk_nframes c2 ->
  (c1, p1) <> (c2, p2) ->
  fk_frame L c1 p1 + fk_fsize c1 <= fk_frame L c2 p2 \/ fk_frame L c2 p2 + fk_fsize c2 <= fk_frame L c1 p1.
Proof.
  intros L c1 p1 c2 p2 H1 P1 H2 P2 NE.
  pose proof (fk_frame_range L c1 p1 H1 P1) as (A1 & B1 & _). pose proof (fk_frame_range L c2 p2 H2 P2) as (A2 & B2 & _).
  destruct (Z.eq_dec c1 c2) as [<-|NC].
  - assert (p1 <> p2) by congruence. unfold fk_frame. pose proof (fk_fsize_pos c1 ltac:(lia)). nia.
  - unfold fk_frames in *. nia.
Qed.
(* [comment removed for export] *)
Lemma fk_flags_disjoint : forall L c1 p1 c2 p2,
  0 <= c1 < FK_NCLS -> 0 <= p1 < fk_nframes c1 -> 0 <= c2 < FK_NCLS -> 0 <= p2 < fk_nframes c2 ->
  (c1, p1) <> (c2, p2) -> fk_flag L c1 p1 <> fk_flag L c2 p2.
Proof.
  intros L c1 p1 c2 p2 H1 P1 H2 P2 NE. unfold fk_flag, fk_flags, FK_NCLS, fk_nframes in *.
  destruct (Z.eq_dec c1 c2) as [<-|NC]; [assert (p1 <> p2) by congruence; lia|].
  pose proof (fk_flags_off c1 ltac:(lia)) as [X1 Y1]. pose proof (fk_flags_off c2 ltac:(lia)) as [X2 Y2].
  (* [comment removed for export] *)
  assert (MONO : forall a b, 0 <= a -> a < b -> b <= 14 -> 32768 - 2 ^ (15 - a) + 2 ^ (14 - a) <= 32768 - 2 ^ (15 - b)).
  { intros a b Ha Hab Hb.
    assert (E : 2 ^ (15 - a) = 2 * 2 ^ (14 - a)) by (replace (15 - a) with (Z.succ (14 - a)) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
    assert (2 ^ (15 - b) <= 2 ^ (14 - a)) by (apply Z.pow_le_mono_r; lia). lia. }
  destruct (Z.lt_ge_cases c1 c2).
  - pose proof (MONO c1 c2 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - pose proof (MONO c2 c1 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afake_geom (L : alayout) : Prop :=
     al_fake L mod 4096 = 0 /\ ablk (al_fake L) (al_fake L + FAKESZ) /\ al_fake L + FAKESZ <= ATOP
  /\ al_dtls L mod 4096 = 0 /\ (sclr (al_dtls L) 4096 /\ iclr (al_dtls L) 4096 /\ 4096 <= al_dtls L) /\ al_dtls L + 4096 <= ATOP
  /\ (sclr (al_t L) 4096 /\ iclr (al_t L) 4096 /\ 4096 <= al_t L) /\ al_t L + 4096 <= ATOP
  /\ (al_fake L + FAKESZ <= al_dtls L \/ al_dtls L + 4096 <= al_fake L)
  /\ (al_t L + 4096 <= al_dtls L \/ al_dtls L + 4096 <= al_t L)
  /\ (al_t L + 4096 <= al_fake L \/ al_fake L + FAKESZ <= al_t L).

(* [comment removed for export] *)
Definition afake_cells (L : alayout) (m : amem) : Prop :=
     rw_cells bsegs m 0xb3ee0 [C8 (Z_to_bv 64 0xac04c)]                                 (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x5ed288 [C8 (Z_to_bv 64 0x5ed2b0); C8 (Z_to_bv 64 (al_fake L))]   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x5ed298 [C8 (Z_to_bv 64 (al_dtls L))]                              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x5ed2b8 [C8 (Z_to_bv 64 0x5eda90)]                                 (* [comment removed for export] *)
  /\ rw_cells bsegs m (al_dtls L + 24) [C8 (Z_to_bv 64 0x5ed290)]                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x14beb1 [C1 (Z_to_bv 8 1)]                                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x149d98 [C4 (Z_to_bv 64 0)]                                        (* [comment removed for export] *)
  /\ dc_at m (al_t L + 48) 16.                                                              (* [comment removed for export] *)

End CANSEC1.
Notation FKB c F n := (mkABlock (ABFake c) F n).

Section CANSEC2. Context {rc : runConstT}.
Definition AFAKE (L : alayout) (LB : list ablock) (m : amem) : Prop :=
     afake_geom L
  /\ afake_cells L m
  (* [comment removed for export] *)
  /\ (exists (h0 h1 h2 : word) (hs : list byte), rw_cells bsegs m (al_fake L) [C8 h0; C8 h1; C8 h2; CB 64 hs])
  /\ rw_cells bsegs m (al_fake L + 88) [C8 (Z_to_bv 64 20)]
  /\ rw_cells bsegs m (al_fake L + 96) [C1 (Z_to_bv 8 0)]
  (* [comment removed for export] *)
  /\ dc_at m (al_fake L + 4096) (FAKESZ - 4096)
  /\ dc_at m (shad (al_fake L)) (shlen FAKESZ)
  (* [comment removed for export] *)
  /\ (forall c pos b, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
        m (wa (fk_flag L c pos)) = Some b -> b <> Z_to_bv 8 0 ->
        In (FKB c (fk_frame L c pos) (fk_fsize c)) LB)
  /\ (forall c F n, In (FKB c F n) LB ->
        0 <= c < FK_NCLS /\ n = fk_fsize c /\
        exists pos, 0 <= pos < fk_nframes c /\ F = fk_frame L c pos /\ m (wa (fk_flag L c pos)) = Some (Z_to_bv 8 1)).

(* [comment removed for export] *)
Definition afake_rng (L : alayout) (RNG : footprint) : Prop :=
  rng RNG (al_fake L) FAKESZ /\ rng RNG (shad (al_fake L)) (shlen FAKESZ) /\ rng RNG (al_dtls L) 4096.

Lemma afake_rng_mono : forall L R R', fp_le R R' -> afake_rng L R -> afake_rng L R'.
Proof.
  intros L R R' LE (A & B & C).
  assert (M : forall lo n, rng R lo n -> rng R' lo n).
  { intros lo n (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. }
  repeat split; try apply M; try assumption; destruct A, B, C; tauto.
Qed.

(* [comment removed for export] *)
Definition afake_untouched (L : alayout) (W : list (Z * Z)) : Prop :=
  Forall (fun iv => (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
                 /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
                 /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
                 /\ (snd iv <= 0xb3ee0 \/ 0xb3ee0 + 8 <= fst iv)
                 /\ (snd iv <= 0x5ed288 \/ 0x5ed288 + 16 <= fst iv)
                 /\ (snd iv <= 0x5ed298 \/ 0x5ed298 + 8 <= fst iv)
                 /\ (snd iv <= 0x5ed2b8 \/ 0x5ed2b8 + 8 <= fst iv)
                 /\ (snd iv <= 0x14beb1 \/ 0x14beb1 + 1 <= fst iv)
                 /\ (snd iv <= 0x149d98 \/ 0x149d98 + 4 <= fst iv)) W.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma disjoint_from_Forall : forall W A n,
  Forall (fun iv : Z * Z => snd iv <= A \/ A + n <= fst iv) W -> disjoint_from W A n.
Proof. induction W as [|[lo hi] W IH]; intros A n H; cbn; [exact I|]. inversion H; subst. cbn in *. split; [lia| apply IH; assumption]. Qed.

Lemma munch_outside_range : forall W m m' A n a,
  munch W m m' -> disjoint_from W A n -> A <= a < A + n -> 0 <= a < 2^64 -> m' (wa a) = m (wa a).
Proof.
  intros W m m' A n a MU D Ha Hr. apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; eauto.
Qed.

(* [comment removed for export] *)
Lemma afake_frame : forall L LB m m' W,
  AFAKE L LB m -> munch W m m' -> wmono bsegs m m' -> afake_untouched L W -> AFAKE L LB m'.
Proof.
  intros L LB m m' W (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV) MU WM UT.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold FAKESZ in *.
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1. destruct G5 as (G5s & G5i & G5). destruct G7 as (G7s & G7i & G7). unfold iclr, sclr, AIMG_LO, AIMG_HI, KLS in G5s, G5i, G7s, G7i.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X1).
  assert (DS : disjoint_from W (shad (al_fake L)) (shlen 11571200)) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X2).
  assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X3).
  assert (D1 : disjoint_from W 0xb3ee0 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X4).
  assert (D2 : disjoint_from W 0x5ed288 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X5).
  assert (D3 : disjoint_from W 0x5ed298 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X6).
  assert (D4 : disjoint_from W 0x5ed2b8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X7).
  assert (D5 : disjoint_from W 0x14beb1 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X8).
  assert (D6 : disjoint_from W 0x149d98 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X9).
  split; [exact G|].
  split.
  { destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold afake_cells.
    repeat lazymatch goal with |- _ /\ _ => split end;
      try (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; first [assumption | eapply disjoint_from_sub; [exact DD| lia| lia| lia]]]).
    eapply dc_at_any2; [exact C8| exact WM| clear -G7i; lia]. }   (* [comment removed for export] *)
  split.
  { exists h0, h1, h2, hs. eapply rw_cells_transport; [exact HS| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]. }
  split; [eapply rw_cells_transport; [exact LOG| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply rw_cells_transport; [exact NGC| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
  split.
  { eapply dc_at_any; [exact DC2| exact WM|]. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations; lia. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) in Hb by (assumption || lia). eauto.
  - intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & Hb). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed.

(* [comment removed for export] *)
Lemma afake_blocks : forall L LB LB' m,
  AFAKE L LB m -> (forall c F n, In (FKB c F n) LB' <-> In (FKB c F n) LB) -> AFAKE L LB' m.
Proof.
  intros L LB LB' m (G & CE & HS & LOG & NGC & DC1 & DC2 & FL & LV) EQ.
  split; [exact G|]. split; [exact CE|]. split; [exact HS|]. split; [exact LOG|]. split; [exact NGC|].
  split; [exact DC1|]. split; [exact DC2|]. split.
  - intros c pos b Hc Hp Hb NZ. apply (proj2 (EQ _ _ _)). eapply FL; eauto.
  - intros c F n Hin. apply LV. apply (proj1 (EQ _ _ _)). exact Hin.
Qed.

Lemma afake_heap_cons : forall L LB m p A n, AFAKE L LB m <-> AFAKE L (HB p A n :: LB) m.
Proof.
  intros L LB m p A n. split; intros H; eapply afake_blocks; [exact H| | exact H|]; intros c F k; cbn; split; intros X;
    [destruct X as [X|X]; [discriminate| exact X] | right; exact X | right; exact X | destruct X as [X|X]; [discriminate| exact X]].
Qed.

(* [comment removed for export] *)
Lemma fk_frame_al64 : forall L c pos, al_fake L mod 4096 = 0 -> 0 <= c -> fk_frame L c pos mod 64 = 0.
Proof.
  intros L c pos AL Hc. unfold fk_frame, fk_frames, fk_fsize.
  assert (E : 2 ^ (6 + c) = 64 * 2 ^ c) by (rewrite Z.pow_add_r by lia; reflexivity). rewrite E.
  replace (al_fake L + 36864 + c * 1048576 + pos * (64 * 2 ^ c))
     with (al_fake L + 64 * (576 + c * 16384 + pos * 2 ^ c)) by lia.
  rewrite Z.add_mod by lia. rewrite Z.mul_comm, Z.mod_mul by lia.
  replace (al_fake L mod 64) with 0; [reflexivity|].
  symmetry. apply Z.mod_divide; [lia|]. apply Z.mod_divide in AL; [|lia].
  destruct AL as [k Hk]. exists (k * 64). lia.
Qed.

Lemma afake_lb : forall L LB m c F n, AFAKE L LB m -> In (FKB c F n) LB ->
  0 <= c < FK_NCLS /\ n = fk_fsize c /\ 0 < n /\ F mod 64 = 0
  /\ al_fake L + 36864 <= F /\ F + n <= al_fake L + FAKESZ
  /\ ablk F (F + n) /\ F + n <= ATOP                                  (* [comment removed for export] *)
  /\ exists pos, 0 <= pos < fk_nframes c /\ F = fk_frame L c pos /\ fflag L c F = fk_flag L c pos
     /\ al_fake L + 4096 <= fflag L c F < al_fake L + 36864.
Proof.
  intros L LB m c F n (G & _ & _ & _ & _ & _ & _ & _ & LV) Hin.
  destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & _). pose proof (fk_frame_range L c pos Hc Hp) as (R1 & R2 & R3 & R4).
  destruct G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1. pose proof (fk_fsize_pos c ltac:(lia)).
  pose proof (fk_frame_al64 L c pos G1 ltac:(lia)). pose proof (fflag_frame L c pos ltac:(lia)).
  pose proof (fk_flag_range L c pos Hc Hp). unfold FAKESZ in *. subst F n.
  repeat lazymatch goal with |- _ /\ _ => split end; try lia.
  { eapply ablk_sub; [exact G2 | lia | lia]. }
  exists pos. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma afake_lb_disjoint : forall L LB m c1 F1 n1 c2 F2 n2,
  AFAKE L LB m -> In (FKB c1 F1 n1) LB -> In (FKB c2 F2 n2) LB -> FKB c1 F1 n1 <> FKB c2 F2 n2 ->
  F1 + n1 <= F2 \/ F2 + n2 <= F1.
Proof.
  intros L LB m c1 F1 n1 c2 F2 n2 AF H1 H2 NE.
  destruct AF as (G & _ & _ & _ & _ & _ & _ & _ & LV).
  destruct (LV _ _ _ H1) as (C1 & N1 & p1 & P1 & E1 & _). destruct (LV _ _ _ H2) as (C2 & N2 & p2 & P2 & E2 & _). subst.
  apply fk_frames_disjoint; try assumption. intros E. injection E as <- <-. apply NE. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma afake_flag : forall L LB m c F n, AFAKE L LB m -> In (FKB c F n) LB ->
  rw_cells bsegs m (fflag L c F) [C1 (Z_to_bv 8 1)].
Proof.
  intros L LB m c F n AF Hin. pose proof (afake_lb L LB m c F n AF Hin) as (Hc & _ & _ & _ & _ & _ & _ & _ & pos & Hp & HF & EF & FR).
  destruct AF as (G & _ & _ & _ & _ & DC1 & _ & _ & LV). destruct (LV _ _ _ Hin) as (_ & _ & pos' & Hp' & HF' & B1).
  assert (pos' = pos) as ->.
  { subst F. unfold fk_frame in HF'. pose proof (fk_fsize_pos c ltac:(lia)). nia. }
  rewrite EF. destruct G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1. unfold FAKESZ in *.
  (* [comment removed for export] *)
  destruct (dc_split m (al_fake L + 4096) (fk_flag L c pos - (al_fake L + 4096)) (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096))) ltac:(replace (fk_flag L c pos - (al_fake L + 4096) + (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)))) with (FAKESZ - 4096) by (unfold FAKESZ; lia); exact DC1) ltac:(lia) ltac:(lia)) as [_ D2].
  replace (al_fake L + 4096 + (fk_flag L c pos - (al_fake L + 4096))) with (fk_flag L c pos) in D2 by lia.
  destruct (dc_split m (fk_flag L c pos) 1 (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)) - 1) ltac:(replace (1 + (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)) - 1)) with (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096))) by lia; exact D2) ltac:(lia) ltac:(lia)) as [D3 _].
  destruct (c1_of_dc m _ D3) as [b Hb].
  assert (b = Z_to_bv 8 1) as ->.
  { destruct Hb as [[WF [B0 [B1' BR]]] WR]. specialize (BR 0%nat ltac:(cbn; lia)). cbn in BR. rewrite Z.add_0_r in BR.
    unfold mrd in BR. rewrite B1 in BR. congruence. }
  exact Hb.
Qed.

(* [comment removed for export] *)
Lemma afake_release : forall L LB m c F n,
  AFAKE L (FKB c F n :: LB) m -> ~ In (FKB c F n) LB ->
  AFAKE L LB (write_to_mem m (wa (fflag L c F)) [Z_to_bv 8 0]).
Proof.
  intros L LB m c F n AF NI.
  pose proof (afake_lb L _ m c F n AF ltac:(left; reflexivity)) as (Hc & Hn & Npos & _ & _ & _ & _ & _ & pos & Hp & HF & EF & FR).
  pose proof (afake_flag L _ m c F n AF ltac:(left; reflexivity)) as FB. rewrite EF in FB |- *.
  destruct AF as (G & CE & HS & LOG & NGC & DC1 & DC2 & FL & LV). destruct G as (G1 & G2 & G3 & Grest). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1.
  pose proof Grest as (_ & _ & _ & (_ & G7i & _) & _). unfold iclr, AIMG_LO, AIMG_HI in G7i. unfold FAKESZ in *.
  set (m' := write_to_mem m (wa (fk_flag L c pos)) [Z_to_bv 8 0]).
  assert (MU : munch [(fk_flag L c pos, fk_flag L c pos + 1)] m m').
  { subst m'. apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
  assert (WM : wmono bsegs m m') by (subst m'; apply wmono_write, wmono_refl).
  assert (OUT : forall a, 0 <= a < 2^64 -> a <> fk_flag L c pos -> m' (wa a) = m (wa a)).
  { intros a Ha NE. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  assert (AT : m' (wa (fk_flag L c pos)) = Some (Z_to_bv 8 0)).
  { subst m'. rewrite write_to_mem_spec by (cbn; lia). rewrite wa_unsigned by lia.
    replace (fk_flag L c pos <=? fk_flag L c pos) with true by (symmetry; apply Z.leb_refl).
    cbn [length andb]. rewrite Z.sub_diag.
    replace (fk_flag L c pos <? fk_flag L c pos + Z.of_nat 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  split; [exact (conj G1 (conj G2 (conj G3 Grest)))|].
  split.
  { destruct CE as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8). unfold afake_cells.
    repeat lazymatch goal with |- _ /\ _ => split end;
      try (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; lia]).
    eapply dc_at_any2; [exact X8| exact WM| clear -G7i; lia]. }
  split.
  { destruct HS as (h0 & h1 & h2 & hs & HS). exists h0, h1, h2, hs. eapply rw_cells_transport; [exact HS| exact MU| exact WM| cbn; lia]. }
  split; [eapply rw_cells_transport; [exact LOG| exact MU| exact WM| cbn; lia]|].
  split; [eapply rw_cells_transport; [exact NGC| exact MU| exact WM| cbn; lia]|].
  split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
  split.
  { eapply dc_at_any; [exact DC2| exact WM|]. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations; lia. }
  split.
  - intros c' pos' b Hc' Hp' Hb NZ.
    destruct (Z.eq_dec (fk_flag L c' pos') (fk_flag L c pos)) as [EQ|NE].
    + exfalso. rewrite EQ, AT in Hb. congruence.
    + pose proof (fk_flag_range L c' pos' Hc' Hp'). rewrite OUT in Hb by lia.
      destruct (FL c' pos' b Hc' Hp' Hb NZ) as [E|IN]; [|exact IN].
      exfalso. injection E as <- EF' _. apply NE. subst F. unfold fk_frame in EF'. pose proof (fk_fsize_pos c ltac:(lia)).
      assert (pos' = pos) by nia. subst pos'. reflexivity.
  - intros c' F' n' Hin. destruct (LV c' F' n' ltac:(right; exact Hin)) as (Hc' & Hn' & pos' & Hp' & HF' & B1).
    split; [exact Hc'|]. split; [exact Hn'|]. exists pos'. split; [exact Hp'|]. split; [exact HF'|].
    destruct (Z.eq_dec (fk_flag L c' pos') (fk_flag L c pos)) as [EQ|NE].
    + exfalso. apply NI.
      destruct (Z.eq_dec c' c) as [EC|NC]; [| exfalso; refine (fk_flags_disjoint L c' pos' c pos Hc' Hp' Hc Hp _ EQ); congruence].
      destruct (Z.eq_dec pos' pos) as [EP|NP]; [| exfalso; refine (fk_flags_disjoint L c' pos' c pos Hc' Hp' Hc Hp _ EQ); congruence].
      subst c' pos'. rewrite HF, Hn. rewrite <- HF', <- Hn'. exact Hin.
    + pose proof (fk_flag_range L c' pos' Hc' Hp'). rewrite OUT by lia. exact B1.
Qed.
End CANSEC2.
(* [comment removed for export] *)
