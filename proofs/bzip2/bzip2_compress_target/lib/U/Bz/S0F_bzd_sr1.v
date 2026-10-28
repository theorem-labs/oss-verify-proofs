(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzLemmasT BzLemmasMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith BzWalkArith2 S0_bzd_out. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDOKS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_out S0F_bzd_outS S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_outR S0F_bzd_snr1.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.

(* [comment removed for export] *)
Notation rmask rN1 := (if (rN1 - 1 =? 1)%Z then 1%Z else 0%Z).

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | sf_unhide; unhide_disj; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section SR.
  Variable c : foctx.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation L16 := (b_ll16 (o_cx c)). Notation L4 := (b_ll4 (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation cf := (d_cftab (o_d c)).
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation RO := (FROs c). Notation WB := (FWB c).
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 :=
    (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 (b_s (o_cx c))) s1 a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (b_s (o_cx c) + 1096)) s3 (Z_to_bv 64 (b_s (o_cx c) + 2047))
         (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1)) s8 (Z_to_bv 64 100000) (Z_to_bv 64 (b_s (o_cx c) + 64080)) (Z_to_bv 64 10) t3 t4 t5 t6) (only parsing).
  Hypothesis OK : foctx_ok c. Hypothesis OKS : foctx_okS c.
  Hypothesis KJ : FKjoin c (FROs c).
  Hypothesis KE : FKexit c (FROs c).

  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation CH := (S0F_bzd_snr1.CH c).
  (* [comment removed for export] *)
  Definition DR (p : pst) (rn' : Z) : dst := set8 d0 (p_oc p) (p_ol p) (p_nu p) (p_k0 p) (p_tp p) rn' (p_rt p) (p_cb p).

  (* [comment removed for export] *)
  Definition sinvR (p : pst) : Prop :=
    (0 <= p_cb p < 4294967296)%Z /\ (0 <= p_oc p < 256)%Z /\ (0 <= p_ol p <= 260)%Z /\
    (0 <= p_nu p <= PP + 1)%Z /\ ((0 <= p_k0 p < 256)%Z \/ (p_nu p = 0%Z /\ (cap <= p_tp p)%Z)) /\
    (0 <= p_tp p < 4294967296)%Z /\ (0 <= p_rn p < 2147483648)%Z /\ (0 <= p_rt p < 512)%Z /\
    (0 <= p_av p <= av0)%Z /\ Z.of_nat (length (p_out p)) = (dlen - p_av p)%Z.

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation cPP := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)) + 1)).
  Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)). Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).
  Notation nl16 := (Z_to_bv 64 (18446744073709551615 - b_ll16 (o_cx c))). Notation nl4 := (Z_to_bv 64 (18446744073709551615 - b_ll4 (o_cx c))).

  (* [comment removed for export] *)
  Definition MS_ (f : nat) (p : pst) : Prop :=
    forall (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f)%Z -> (1 <= p_ol p)%Z ->
      evt s0segs (KQ (K_PM f (D p) (Ss p)))
        (MS (RR ra t0 t1 t2 a0 cstrm a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) F (Z_to_bv 64 0x14fe4) fc None m (seg_rom s0segs)).
  (* [comment removed for export] *)
  Definition HS (f : nat) (p : pst) : Prop :=
    forall (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f)%Z ->
      evt s0segs (KQ (K_PM f (D p) (Ss p)))
        (MS (RR ra t0 t1 t2 (Z_to_bv 64 (p_av p)) cstrm a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) F (Z_to_bv 64 0x14860) fc None m (seg_rom s0segs)).
  (* [comment removed for export] *)
  Definition OUTS (f : nat) (p : pst) : Prop :=
    forall (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f)%Z -> (1 <= p_av p)%Z -> (1 <= p_ol p)%Z ->
      evt s0segs (KQ (K_PH f (D p) (Ss p)))
        (MS (RR ra t0 t1 t2 a0 cstrm a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) F (Z_to_bv 64 0x14870) fc None m (seg_rom s0segs)).
  (* [comment removed for export] *)
  Definition GS (f : nat) (p : pst) : Prop :=
    forall (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f)%Z -> (1 <= p_av p)%Z -> p_ol p = 0%Z ->
      evt s0segs (KQ (K_PG f (D p) (Ss p)))
        (MS (RR ra t0 t1 t2 a0 cstrm a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) F (Z_to_bv 64 0x1492c) fc None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition T1S (f' : nat) (p : pst) : Prop :=
    forall (ra t0 t2 a0 a5 s1 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f' + 1)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 1%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (p_nu p < PP)%Z -> (p_tp p < cap)%Z ->
      evt s0segs (KQ (PG1 (Datatypes.S f') PP (D p) (Ss p)))
        (MS (RR ra t0 (Z_to_bv 64 (p_tp p)) t2 a0 cstrm cPP cnn (Z_to_bv 64 (p_k0 p)) a5 (Z_to_bv 64 (p_nu p))
                (Z_to_bv 64 (indexIntoF (p_tp p) cf)) s1 cm4 s8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x149f0) fc None m (seg_rom s0segs)).
  Definition R1S (f' : nat) (p : pst) : Prop :=
    forall (ra s1 s8 t3 t4 t5 t6 : word) (nb rN1 v16 : Z) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f' + 1)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 1%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (p_nu p < PP)%Z -> (p_tp p < 1048576)%Z ->
      (0 <= nb <= 255)%Z -> (1 <= rN1 < 2147483648)%Z -> (0 <= v16 < 65536)%Z -> Z.land (v16 * 4) 4 = Z.land (p_tp p * 4) 4 ->
      evt s0segs (KQ (PG1b (Datatypes.S f') PP (Z.lxor nb (rmask rN1)) (DR p (rN1 - 1)) (Ss p)))
        (MS (RR ra (Z_to_bv 64 v16) (Z_to_bv 64 rN1) (Z_to_bv 64 (p_tp p)) cl16 cstrm cPP cnn (Z_to_bv 64 (p_k0 p)) cl4
                (Z_to_bv 64 (p_nu p)) (Z_to_bv 64 nb) s1 cm4 s8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14ad4) fc None m (seg_rom s0segs)).
  (* [comment removed for export] *)
  Definition T2S (f' : nat) (p : pst) : Prop :=
    forall (ra a6 a7 s1 s8 t3 t5 : word) (v16 : Z) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f')%Z -> (1 <= p_av p)%Z ->
      p_ol p = 2%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (1 <= p_nu p < PP)%Z -> (p_tp p < cap)%Z ->
      (0 <= v16 < 65536)%Z -> Z.land (v16 * 4) 4 = Z.land (p_tp p * 4) 4 ->
      evt s0segs (KQ (PG2 (Datatypes.S f') PP (D p) (Ss p)))
        (MS (RR ra (Z_to_bv 64 v16) (Z_to_bv 64 (p_nu p)) (Z_to_bv 64 (p_tp p)) cl16 cstrm cPP cnn (Z_to_bv 64 (p_k0 p)) cl4 a6 a7
                s1 cm4 s8 t3 (Z_to_bv 64 (indexIntoF (p_tp p) cf)) t5 (Z_to_bv 64 (p_rn p)))
            F (Z_to_bv 64 0x14b90) fc None m (seg_rom s0segs)).
  Definition R2S (f' : nat) (p : pst) : Prop :=
    forall (ra t0 a7 s1 s8 : word) (nb rN1 v16 : Z) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f')%Z -> (1 <= p_av p)%Z ->
      p_ol p = 2%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (1 <= p_nu p < PP)%Z -> (p_tp p < 1048576)%Z ->
      (0 <= nb <= 255)%Z -> (1 <= rN1 < 2147483648)%Z -> (0 <= v16 < 65536)%Z -> Z.land (v16 * 4) 4 = Z.land (p_tp p * 4) 4 ->
      evt s0segs (KQ (PG2b (Datatypes.S f') PP (Z.lxor nb (rmask rN1)) (DR p (rN1 - 1)) (Ss p)))
        (MS (RR ra t0 (Z_to_bv 64 (p_nu p)) (Z_to_bv 64 v16) cl16 cstrm cPP cnn (Z_to_bv 64 (p_k0 p)) cl4 nl16 a7
                s1 cm4 s8 nl4 (Z_to_bv 64 nb) (Z_to_bv 64 (p_tp p)) (Z_to_bv 64 rN1))
            F (Z_to_bv 64 0x14c38) fc None m (seg_rom s0segs)).
  (* [comment removed for export] *)
  Definition T3S (f' : nat) (p : pst) : Prop :=
    forall (t1 s1 s8 t4 t6 : word) (v16 : Z) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f' - 1)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 3%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (2 <= p_nu p < PP)%Z -> (p_tp p < cap)%Z ->
      (0 <= v16 < 65536)%Z -> Z.land (v16 * 4) 4 = Z.land (p_tp p * 4) 4 ->
      evt s0segs (KQ (PG3 (Datatypes.S f') PP (D p) (Ss p)))
        (MS (RR (Z_to_bv 64 (p_rn p)) (Z_to_bv 64 (indexIntoF (p_tp p) cf)) t1 (Z_to_bv 64 v16) cl16 cstrm cPP cnn (Z_to_bv 64 (p_k0 p)) cl4 nl16
                (Z_to_bv 64 (p_nu p)) s1 cm4 s8 nl4 t4 (Z_to_bv 64 (p_tp p)) t6)
            F (Z_to_bv 64 0x14cf8) fc None m (seg_rom s0segs)).
  Definition R3S (f' : nat) (p : pst) : Prop :=
    forall (t1 t2 a5 a6 s1 s8 t3 t4 t5 t6 : word) (nb rN1 : Z) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f' - 1)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 3%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (2 <= p_nu p < PP)%Z -> (p_tp p < 1048576)%Z ->
      (0 <= nb <= 255)%Z -> (1 <= rN1 < 2147483648)%Z ->
      evt s0segs (KQ (PG3b (Datatypes.S f') PP (Z.lxor nb (rmask rN1)) (DR p (rN1 - 1)) (Ss p)))
        (MS (RR (Z_to_bv 64 rN1) (Z_to_bv 64 nb) t1 t2 (Z_to_bv 64 (p_tp p)) cstrm cPP cnn (Z_to_bv 64 (p_k0 p)) a5 a6
                (Z_to_bv 64 (p_nu p)) s1 cm4 s8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14d98) fc None m (seg_rom s0segs)).
  (* [comment removed for export] *)
  Definition T4S (f' : nat) (p : pst) : Prop :=
    forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f' - 2)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 3%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (3 <= p_nu p < PP)%Z -> (p_tp p < cap)%Z ->
      evt s0segs (KQ (PG4 (Datatypes.S f') (D p) (Ss p)))
        (MS (RR ra t0 t1 t2 (Z_to_bv 64 (indexIntoF (p_tp p) cf)) a1 a2 a3 a4 a5 a6 a7 s1 cm4 s8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14dd4) fc None m (seg_rom s0segs)).
  Definition R4S (f' : nat) (p : pst) : Prop :=
    forall (ra t0 t1 t2 a3 a4 a5 a6 a7 s1 s8 t3 t4 t5 t6 : word) (nb rN1 : Z) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f' - 2)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 3%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (3 <= p_nu p < PP)%Z -> (p_tp p < 1048576)%Z ->
      (0 <= nb <= 255)%Z -> (1 <= rN1 < 2147483648)%Z ->
      evt s0segs (KQ (PG4b (Datatypes.S f') (Z.lxor nb (rmask rN1)) (DR p (rN1 - 1)) (Ss p)))
        (MS (RR ra t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 (p_tp p)) (Z_to_bv 64 rN1) a3 a4 a5 a6 a7 s1 cm4 s8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14e98) fc None m (seg_rom s0segs)).
  (* [comment removed for export] *)
  Definition T5S (f' : nat) (p : pst) : Prop :=
    forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f' - 3)%Z -> (1 <= p_av p)%Z ->
      (4 <= p_ol p <= 259)%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (4 <= p_nu p <= PP)%Z -> (p_tp p < cap)%Z ->
      evt s0segs (KQ (PG5 (Datatypes.S f') (D p) (Ss p)))
        (MS (RR ra t0 t1 t2 (Z_to_bv 64 (indexIntoF (p_tp p) cf)) a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14ee4) fc None m (seg_rom s0segs)).
  (* [comment removed for export] *)
  Definition R5S (f' : nat) (p : pst) : Prop :=
    forall (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (rN1 : Z) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f' - 3)%Z -> (1 <= p_av p)%Z ->
      (4 <= p_ol p <= 259)%Z -> (0 <= p_k0 p < 256)%Z -> (4 <= p_nu p <= PP)%Z -> (p_tp p < 1048576)%Z ->
      (1 <= rN1 < 2147483648)%Z ->
      evt s0segs (KQ (K_PM f' (set8 d0 (p_oc p) (p_ol p) (p_nu p + 1) (Z.lxor (p_k0 p) (rmask rN1)) (p_tp p) (rN1 - 1) (p_rt p) (p_cb p)) (Ss p)))
        (MS (RR ra t0 t1 t2 (Z_to_bv 64 (p_k0 p)) (Z_to_bv 64 rN1) a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14fac) fc None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & L16A & L4A & CFA & CRC & RNA & GOT & MI); unfold FGOT in GOT.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac unCH H := let DSm := fresh "DSm" in let DE := fresh "DE" in let ROm := fresh "ROm" in
    cps_destruct H as (DSm & DE & ROm & MU & WM); unDS DSm; cps_destruct DE as (DSTA & DL & Edb & Lout); unRO ROm.
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & SEP_SD & IAS & IAD & JWF & ENT);
    let OKS' := fresh "OKS" in pose proof OKS as OKS';
    cps_destruct OKS' as (HSM & HL16 & HL4 & SEP_S16 & SEP_D16 & SEP_S4 & SEP_D4 & SEP_164);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & Rcf & Rtt & Rl16 & Rl4);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold FWB in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length cf 257 ltac:(lia)) as CFL;
    pose proof (zh16_length (d_ll16 d0) (200000 * n) ltac:(lia)) as L16L; pose proof (zb8_length (d_ll4 d0) (50000 * n) ltac:(lia)) as L4L;
    pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL; hide_disj.
  Ltac ro_close := unfold FROs, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.

  (* [comment removed for export] *)
  Ltac cf_load i :=
    lazymatch goal with CFA : u32arr _ ?mm (S + 1096)%Z _, Rcf : _ -> forall i0 : Z, _ |- _ =>
      let RD := fresh "RD" in let CR := fresh "CFR" in
      pose proof (Rcf ltac:(lia) i ltac:(lia)) as CR;
      pose proof (zw32_read s0segs mm (S + 1096)%Z cf 257 i _ CFA ltac:(lia) eq_refl) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (zget cf i)) by lia end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_B1 : forall (P : machine_state -> Prop) (m : word -> option byte) (idx : Z)
      (ra t1 a1 a2 a3 a4 a6 s1 s3 s8 t5 t6 : word),
    RO m -> (0 <= idx < 2147483648)%Z ->
    (forall (t0 t2 t3 t4 : word) (lo hi : Z), iif_state (zget cf) idx 8 = (lo, hi) ->
       evt s0segs P (MS (RR ra t0 t1 t2 (Z_to_bv 64 idx) a1 a2 a3 a4 (Z_to_bv 64 hi) a6 (Z_to_bv 64 lo) s1 s3 s8 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x149f0) fc None m (seg_rom s0segs))) ->
    forall (k t : nat) (lo hi : Z) (t0 t2 t3 t4 : word), (t + k = 7)%nat -> iif_state (zget cf) idx t = (lo, hi) ->
      evt s0segs P (MS (RR ra t0 t1 t2 (Z_to_bv 64 idx) a1 a2 a3 a4 (Z_to_bv 64 hi) a6 (Z_to_bv 64 lo) s1 s3 s8 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x14980) fc None m (seg_rom s0segs)).
  Proof.
    intros P m idx. intros until t6. intros ROm Hidx EXIT k.
    induction k as [|k IH]; intros t lo hi t0 t2 t3 t4 Hk E; unRO ROm; prep;
      pose proof (iif_stepW (zget cf) idx t lo hi ltac:(lia) E) as SW; cbv zeta in SW;
      cps_destruct SW as (A & B & Cm & Dh & E1 & XT).
    - (* [comment removed for export] *)
      assert (Ht7 : t = 7%nat) by lia. subst t.
      wstep. wstep. wstep. notrap.
      wstep. wstep. wstep. wstep. notrap.
      fstep. fstep. wstep. wstep. wstep. notrap.
      cf_load ((lo + hi) / 2)%Z.
      wstep. wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + (* [comment removed for export] *)
        replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [| exfalso; lia].
        wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        eapply EXIT. exact E1.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [exfalso; lia|].
        wstep. wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        eapply EXIT. exact E1.
    - wstep. wstep. wstep. notrap.
      wstep. wstep. wstep. wstep. notrap.
      fstep. fstep. wstep. wstep. wstep. notrap.
      cf_load ((lo + hi) / 2)%Z.
      wstep. wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [| exfalso; lia].
        wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [exfalso; lia|].
        wstep. wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
  Time Qed.

  (* [comment removed for export] *)
  Lemma sr_B2 : forall (P : machine_state -> Prop) (m : word -> option byte) (idx : Z)
      (ra t0 t1 a0 a1 a2 a3 a4 a5 s1 s3 t6 : word),
    RO m -> (0 <= idx < 2147483648)%Z ->
    (forall (a7 s8 t3 t5 : word) (lo hi : Z), iif_state (zget cf) idx 8 = (lo, hi) ->
       evt s0segs P (MS (RR ra t0 t1 (Z_to_bv 64 idx) a0 a1 a2 a3 a4 a5 (Z_to_bv 64 hi) a7 s1 s3 s8 t3 (Z_to_bv 64 lo) t5 t6)
                       F (Z_to_bv 64 0x14b90) fc None m (seg_rom s0segs))) ->
    forall (k t : nat) (lo hi : Z) (a7 s8 t3 t5 : word), (t + k = 7)%nat -> iif_state (zget cf) idx t = (lo, hi) ->
      evt s0segs P (MS (RR ra t0 t1 (Z_to_bv 64 idx) a0 a1 a2 a3 a4 a5 (Z_to_bv 64 hi) a7 s1 s3 s8 t3 (Z_to_bv 64 lo) t5 t6)
                      F (Z_to_bv 64 0x14b20) fc None m (seg_rom s0segs)).
  Proof.
    intros P m idx. intros until t6. intros ROm Hidx EXIT k.
    induction k as [|k IH]; intros t lo hi a7 s8 t3 t5 Hk E; unRO ROm; prep;
      pose proof (iif_stepW (zget cf) idx t lo hi ltac:(lia) E) as SW; cbv zeta in SW;
      cps_destruct SW as (A & B & Cm & Dh & E1 & XT).
    - (* [comment removed for export] *)
      assert (Ht7 : t = 7%nat) by lia. subst t.
      wstep. wstep. wstep. notrap.
      wstep. wstep. wstep. wstep. notrap.
      fstep. fstep. wstep. wstep. wstep. notrap.
      cf_load ((lo + hi) / 2)%Z.
      wstep. wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + (* [comment removed for export] *)
        replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [| exfalso; lia].
        wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        eapply EXIT. exact E1.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [exfalso; lia|].
        wstep. wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        eapply EXIT. exact E1.
    - wstep. wstep. wstep. notrap.
      wstep. wstep. wstep. wstep. notrap.
      fstep. fstep. wstep. wstep. wstep. notrap.
      cf_load ((lo + hi) / 2)%Z.
      wstep. wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [| exfalso; lia].
        wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [exfalso; lia|].
        wstep. wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
  Time Qed.

  (* [comment removed for export] *)
  Lemma sr_B3 : forall (P : machine_state -> Prop) (m : word -> option byte) (idx : Z)
      (ra t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 : word),
    RO m -> (0 <= idx < 2147483648)%Z ->
    (forall (s1 s8 t4 t6 : word) (lo hi : Z), iif_state (zget cf) idx 8 = (lo, hi) ->
       evt s0segs P (MS (RR ra (Z_to_bv 64 lo) (Z_to_bv 64 hi) t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 (Z_to_bv 64 idx) t6)
                       F (Z_to_bv 64 0x14cf8) fc None m (seg_rom s0segs))) ->
    forall (k t : nat) (lo hi : Z) (s1 s8 t4 t6 : word), (t + k = 7)%nat -> iif_state (zget cf) idx t = (lo, hi) ->
      evt s0segs P (MS (RR ra (Z_to_bv 64 lo) (Z_to_bv 64 hi) t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 (Z_to_bv 64 idx) t6)
                      F (Z_to_bv 64 0x14c88) fc None m (seg_rom s0segs)).
  Proof.
    intros P m idx. intros until t3. intros ROm Hidx EXIT k.
    induction k as [|k IH]; intros t lo hi s1 s8 t4 t6 Hk E; unRO ROm; prep;
      pose proof (iif_stepW (zget cf) idx t lo hi ltac:(lia) E) as SW; cbv zeta in SW;
      cps_destruct SW as (A & B & Cm & Dh & E1 & XT).
    - (* [comment removed for export] *)
      assert (Ht7 : t = 7%nat) by lia. subst t.
      wstep. wstep. wstep. notrap.
      wstep. wstep. wstep. wstep. notrap.
      fstep. fstep. wstep. wstep. wstep. notrap.
      cf_load ((lo + hi) / 2)%Z.
      wstep. wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + (* [comment removed for export] *)
        replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [| exfalso; lia].
        wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        eapply EXIT. exact E1.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [exfalso; lia|].
        wstep. wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        eapply EXIT. exact E1.
    - wstep. wstep. wstep. notrap.
      wstep. wstep. wstep. wstep. notrap.
      fstep. fstep. wstep. wstep. wstep. notrap.
      cf_load ((lo + hi) / 2)%Z.
      wstep. wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [| exfalso; lia].
        wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. if_cases K'; zify_cond K'; rewrite ?signed_lit_small in K' by lia; [exfalso; lia|].
        wstep. wstep. wstep. wstep. notrap. wstep. wstep. wstep.
        if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
  Time Qed.

End SR.
End ACeilS1.
