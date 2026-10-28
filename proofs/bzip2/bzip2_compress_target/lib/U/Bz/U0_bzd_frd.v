(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzLemmasT BzLemmasMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith S0_bzd_out. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_out.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_vspec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_fr3.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac tlia ::= RelLiaS.tlia_bzd_r.
Local Ltac BzSepTac.tlia1 ::= RelLiaS.tlia1_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ACeilS1. Context {ACEIL__ : ACeil}.

Section FR.
  Variable c : foctx.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation TT := (b_tt (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation RO := (FROf c). Notation WB := (FWB c).
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 :=
    (FRR c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) (only parsing).
  Notation csnb := (Z_to_bv 64 snb). Notation cnn := (Z_to_bv 64 (n * 100000)). Notation cstrm := (Z_to_bv 64 STRM).
  Notation cm4 := (Z_to_bv 64 (-4)). Notation ctt := (Z_to_bv 64 TT). Notation cpp := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)) + 1)).
  Notation cntt := (Z_to_bv 64 (18446744073709551615 - b_tt (o_cx c))).
  Notation D8 oc ol nu k0 tp rn rt cb := (set8 (o_d c) oc ol nu k0 tp rn rt cb).
  Notation S3 out av tout := (smod (o_s c) out av tout).
  Notation JJ tol toh := (jk_set_o (o_J c) tol toh).
  Notation KB w r := (Z.lxor (Z.land w 255) (if (r - 1 =? 1)%Z then 1%Z else 0%Z)).
  Hypothesis OK : foctx_ok c. Hypothesis OKF : foctx_okF c. Hypothesis AL : foctx_al c.
  Hypothesis RD1 : d_rand (o_d c) = 1%Z.
  Hypothesis KJ : FKjoin c (FROf c).
  Hypothesis KE : FKexit c (FROf c).

  Notation finv := (S0F_bzd_fr1.finv c).

  Definition MA (f : nat) : Prop :=
    forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc ol nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      DSg c m (JJ tol toh) (D8 oc ol nu k0 tp rn rt cb) (S3 out av tout) -> DESTg c m (S3 out av tout) dbytes rest ->
      RO m -> munch WB m0 m -> wmono s0segs m0 m ->
      finv oc ol nu k0 tp rn rt cb av -> (PP - nu <= Z.of_nat f)%Z ->
      evt s0segs (KQ (K_PM f (D8 oc ol nu k0 tp rn rt cb) (S3 out av tout)))
          (MS (RR ra t0 t1 t2 cstrm a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) F (Z_to_bv 64 0x15018) fc None m (seg_rom s0segs)).

  Definition MB (f : nat) : Prop :=
    forall (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc ol nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      DSg c m (JJ tol toh) (D8 oc ol nu k0 tp rn rt cb) (S3 out av tout) -> DESTg c m (S3 out av tout) dbytes rest ->
      RO m -> munch WB m0 m -> wmono s0segs m0 m ->
      finv oc ol nu k0 tp rn rt cb av -> (PP - nu <= Z.of_nat f)%Z ->
      evt s0segs (KQ (K_PM f (D8 oc ol nu k0 tp rn rt cb) (S3 out av tout)))
          (MS (RR ra t0 t1 t2 cstrm (Z_to_bv 64 av) a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) F (Z_to_bv 64 0x1501c) fc None m (seg_rom s0segs)).

  Definition GS (f : nat) : Prop :=
    forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      DSg c m (JJ tol toh) (D8 oc 0 nu k0 tp rn rt cb) (S3 out av tout) -> DESTg c m (S3 out av tout) dbytes rest ->
      RO m -> munch WB m0 m -> wmono s0segs m0 m ->
      finv oc 0 nu k0 tp rn rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z ->
      evt s0segs (KQ (K_PG f (D8 oc 0 nu k0 tp rn rt cb) (S3 out av tout)))
          (MS (RR ra t0 t1 t2 cstrm a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) F (Z_to_bv 64 0x150cc) fc None m (seg_rom s0segs)).

  Definition R1S (f : nat) : Prop :=
    forall (ra t1 t2 s1 s8 t3 t4 t5 t6 : word) (m : word -> option byte)
           (nu k0 rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (w rN1 : Z) (dbytes rest : list byte),
      DSg c m (JJ tol toh) (D8 k0 1 nu k0 (w / 256) rn rt cb) (S3 out av tout) -> DESTg c m (S3 out av tout) dbytes rest ->
      RO m -> munch WB m0 m -> wmono s0segs m0 m ->
      finv k0 1 nu k0 (w / 256) rn rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z -> (0 <= k0 < 256)%Z ->
      (0 <= nu < PP)%Z -> (0 <= w < 4294967296)%Z -> (1 <= rN1 < 2147483648)%Z ->
      evt s0segs (KQ (PG1b f PP (KB w rN1) (D8 k0 1 nu k0 (w / 256) (rN1 - 1) rt cb) (S3 out av tout)))
          (MS (RR ra (Z_to_bv 64 w) t1 t2 cstrm cnn ctt cpp (Z_to_bv 64 k0) (Z_to_bv 64 nu) (Z_to_bv 64 rN1) (Z_to_bv 64 (w / 256))
                  s1 cm4 s8 t3 t4 t5 t6)
              F (Z_to_bv 64 0x15190) fc None m (seg_rom s0segs)).

  Definition R2S (f : nat) : Prop :=
    forall (ra t2 a7 s1 s8 t4 t5 t6 : word) (m : word -> option byte)
           (nu k0 rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (w rN1 : Z) (dbytes rest : list byte),
      DSg c m (JJ tol toh) (D8 k0 2 (nu + 1) k0 (w / 256) rn rt cb) (S3 out av tout) -> DESTg c m (S3 out av tout) dbytes rest ->
      RO m -> munch WB m0 m -> wmono s0segs m0 m ->
      finv k0 2 (nu + 1) k0 (w / 256) rn rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z -> (0 <= k0 < 256)%Z ->
      (0 <= nu /\ nu + 1 < PP)%Z -> (0 <= w < 4294967296)%Z -> (1 <= rN1 < 2147483648)%Z ->
      evt s0segs (KQ (PG2b f PP (KB w rN1) (D8 k0 2 (nu + 1) k0 (w / 256) (rN1 - 1) rt cb) (S3 out av tout)))
          (MS (RR ra (Z_to_bv 64 (w / 256)) (Z_to_bv 64 rN1) t2 cstrm cnn ctt cpp (Z_to_bv 64 k0) cntt (Z_to_bv 64 (nu + 1)) a7
                  s1 cm4 s8 (Z_to_bv 64 w) t4 t5 t6)
              F (Z_to_bv 64 0x15234) fc None m (seg_rom s0segs)).

  Definition R3S (f : nat) : Prop :=
    forall (ra a6 s1 s8 t3 t4 t5 t6 : word) (m : word -> option byte)
           (nu k0 rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (w rN1 : Z) (dbytes rest : list byte),
      DSg c m (JJ tol toh) (D8 k0 3 (nu + 2) k0 (w / 256) rn rt cb) (S3 out av tout) -> DESTg c m (S3 out av tout) dbytes rest ->
      RO m -> munch WB m0 m -> wmono s0segs m0 m ->
      finv k0 3 (nu + 2) k0 (w / 256) rn rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z -> (0 <= k0 < 256)%Z ->
      (0 <= nu /\ nu + 2 < PP)%Z -> (0 <= w < 4294967296)%Z -> (1 <= rN1 < 2147483648)%Z ->
      evt s0segs (KQ (PG3b f PP (KB w rN1) (D8 k0 3 (nu + 2) k0 (w / 256) (rN1 - 1) rt cb) (S3 out av tout)))
          (MS (RR ra (Z_to_bv 64 (w / 256)) (Z_to_bv 64 w) (Z_to_bv 64 rN1) cstrm cnn ctt cpp (Z_to_bv 64 k0) cntt a6 (Z_to_bv 64 (nu + 2))
                  s1 cm4 s8 t3 t4 t5 t6)
              F (Z_to_bv 64 0x152d8) fc None m (seg_rom s0segs)).

  Definition R4S (f : nat) : Prop :=
    forall (ra t1 t2 a3 a7 s1 s8 t4 t5 t6 : word) (m : word -> option byte)
           (nu k0 rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (w rN1 : Z) (dbytes rest : list byte),
      DSg c m (JJ tol toh) (D8 k0 3 (nu + 3) k0 (w / 256) rn rt cb) (S3 out av tout) -> DESTg c m (S3 out av tout) dbytes rest ->
      RO m -> munch WB m0 m -> wmono s0segs m0 m ->
      finv k0 3 (nu + 3) k0 (w / 256) rn rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z -> (0 <= k0 < 256)%Z ->
      (0 <= nu /\ nu + 3 < PP)%Z -> (0 <= w < 4294967296)%Z -> (1 <= rN1 < 2147483648)%Z ->
      evt s0segs (KQ (PG4b f (KB w rN1) (D8 k0 3 (nu + 3) k0 (w / 256) (rN1 - 1) rt cb) (S3 out av tout)))
          (MS (RR ra (Z_to_bv 64 w) t1 t2 cstrm cnn ctt a3 (Z_to_bv 64 (w / 256)) cntt (Z_to_bv 64 (nu + 3)) a7
                  s1 cm4 s8 (Z_to_bv 64 rN1) t4 t5 t6)
              F (Z_to_bv 64 0x15374) fc None m (seg_rom s0segs)).

  Definition R5S (f : nat) : Prop :=
    forall (ra t0 t1 t2 a2 a4 a5 a6 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc ol nu rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (w rN1 : Z) (dbytes rest : list byte),
      DSg c m (JJ tol toh) (D8 oc ol (nu + 4) (Z.land w 255) (w / 256) rn rt cb) (S3 out av tout) -> DESTg c m (S3 out av tout) dbytes rest ->
      RO m -> munch WB m0 m -> wmono s0segs m0 m ->
      finv oc ol (nu + 4) (Z.land w 255) (w / 256) rn rt cb av -> (PP - nu <= Z.of_nat f)%Z -> (1 <= av)%Z ->
      (0 <= nu /\ nu + 3 < PP)%Z -> (0 <= w < 4294967296)%Z -> (1 <= rN1 < 2147483648)%Z -> (4 <= ol <= 259)%Z ->
      evt s0segs (KQ (PG5b f (KB w rN1) (D8 oc ol (nu + 4) (Z.land w 255) (w / 256) (rN1 - 1) rt cb) (S3 out av tout)))
          (MS (RR ra t0 t1 t2 cstrm (Z_to_bv 64 (Z.land w 255)) a2 (Z_to_bv 64 (nu + 4)) a4 a5 a6 (Z_to_bv 64 rN1)
                  s1 s3 s8 t3 t4 t5 t6)
              F (Z_to_bv 64 0x15418) fc None m (seg_rom s0segs)).
End FR.
End ACeilS1.
