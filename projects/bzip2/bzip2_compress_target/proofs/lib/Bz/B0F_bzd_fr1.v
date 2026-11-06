(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzWalkArith BzWalkArith2 S0_bzd_out BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDOKS DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out S0F_bzd_outS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_fr3.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac2 AsanKit AsanCut AsanCutB0 AsanKitB0 DecCutB B0F_decV B0F_bzdV B0F_bzd_uV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_outS S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_fr3 S0F_bzd_outR S0F_bzd_snr1 S0F_bzd_sr1.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLiaS.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold; AsanKit.sh_norm.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section FR.
  Variable c : foctx.
  Variable SHS : Z. Variable w0 w8 w40 w48 w56 w64 w72 w88 : word.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation TT := (b_tt (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation uspi := (bv_unsigned (o_SP c)).
  Notation RO := (FROfA DI_B0 c). Notation WB := (FWBA c).
  Hypothesis OK : foctx_okA c BIHI0. Hypothesis OKF : foctx_okFA c BIHI0. Hypothesis ALT : (b_tt (o_cx c) mod 4 = 0)%Z.
  Hypothesis ANS : sanchor S SHS.
  Hypothesis SH : obz_sh DI_B0 c WB m0.
  Hypothesis KJ : B0_FKjoin c SHS w0 (FROfA DI_B0 c) (FWBA c).
  Hypothesis KE : B0_FKexit c SHS w0 (FROfA DI_B0 c) (FWBA c).
  Hypothesis RD1 : d_rand (o_d c) = 1%Z.

  Notation pst := S0F_bzd_snr1.pst. Notation PST := S0F_bzd_snr1.PST.
  Notation p_oc := S0F_bzd_snr1.p_oc. Notation p_ol := S0F_bzd_snr1.p_ol. Notation p_nu := S0F_bzd_snr1.p_nu. Notation p_k0 := S0F_bzd_snr1.p_k0.
  Notation p_tp := S0F_bzd_snr1.p_tp. Notation p_rn := S0F_bzd_snr1.p_rn. Notation p_rt := S0F_bzd_snr1.p_rt. Notation p_cb := S0F_bzd_snr1.p_cb.
  Notation p_out := S0F_bzd_snr1.p_out. Notation p_av := S0F_bzd_snr1.p_av. Notation p_tout := S0F_bzd_snr1.p_tout.
  Notation p_tol := S0F_bzd_snr1.p_tol. Notation p_toh := S0F_bzd_snr1.p_toh.
  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation sinvR := (S0F_bzd_sr1.sinvR c). Notation DR := (S0F_bzd_sr1.DR c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation csnb := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)))).
  Notation cpp := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)) + 1)). Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)).
  Notation cm4 := (Z_to_bv 64 (-4)).
  Notation ctt := (Z_to_bv 64 (b_tt (o_cx c))).
  Notation cntt := (Z_to_bv 64 (18446744073709551615 - b_tt (o_cx c))).   (* [comment removed for export] *)
  Notation hs7 := (Z_to_bv 64 (SHS + -2147450878)).   (* [comment removed for export] *)
  Notation hs9 := (Z_to_bv 64 (SHS + -2147450879)).   (* [comment removed for export] *)
  Notation c16 := (Z_to_bv 64 (SHS + 2)).             (* [comment removed for export] *)
  Notation c24 := (Z_to_bv 64 (SHS + 3)).             (* [comment removed for export] *)
  Notation c60 := (Z_to_bv 64 (SHS + 7)).             (* [comment removed for export] *)
  Notation c64 := (Z_to_bv 64 (SHS + 8)).             (* [comment removed for export] *)
  Notation cnu := (Z_to_bv 64 (SHS + 136)).           (* [comment removed for export] *)

  (* [comment removed for export] *)

  Definition FSLs (m : word -> option byte) : Prop :=
    rw_cells b0segs m uspi
      (bzd_slots S SHS w0 w8 w40 w48 w56 w64 w72 w88 (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870))).
  (* [comment removed for export] *)
  Definition CHf (m : word -> option byte) (p : pst) (dbytes rest : list byte) : Prop :=
    DSgA DI_B0 c m (Jp p) (D p) (Ss p) /\ DESTgA DI_B0 c m (Ss p) dbytes rest /\ FSLs m /\ RO m /\ munch WB m0 m /\ wmono b0segs m0 m.

  (* [comment removed for export] *)
  Definition H0S (f : nat) (p : pst) : Prop :=
    forall (ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s3 s5 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CHf m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f)%Z ->
      evt b0segs (KQ (K_PM f (D p) (Ss p)))
        (MS (B0RR c SHS ra t0 t1 t2 (Z_to_bv 64 (STRM + 32)) a1 cstrm a3 a4 a5 a6 a7 s3 s5 hs7 hs9 t3 t4 t5 t6)
            F (Z_to_bv 64 0x855c4) fc None m (seg_rom b0segs)).
  (* [comment removed for export] *)
  Definition GS (f : nat) (p : pst) : Prop :=
    forall (ra t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s5 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CHf m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f)%Z -> (1 <= p_av p)%Z -> p_ol p = 0%Z ->
      evt b0segs (KQ (K_PG f (D p) (Ss p)))
        (MS (B0RR c SHS ra t0 t1 t2 a0 a1 a2 c16 a4 a5 a6 a7 s3 s5 hs7 hs9 t3 t4 t5 t6)
            F (Z_to_bv 64 0x85830) fc None m (seg_rom b0segs)).
  (* [comment removed for export] *)
  Definition R1S (f : nat) (p : pst) : Prop :=
    forall (a0 s3 s5 t3 t6 : word) (w : Z) (m : word -> option byte) (dbytes rest : list byte),
      CHf m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f + 1)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 1%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (p_nu p < PP)%Z ->
      (0 <= w < 4294967296)%Z -> p_tp p = (w / 256)%Z -> (1 <= p_rn p)%Z ->
      evt b0segs (KQ (PG1b (Datatypes.S f) PP (Z.lxor (Z.land w 255) (rmask (p_rn p))) (DR p (p_rn p - 1)) (Ss p)))
        (MS (B0RR c SHS cm4 cpp (Z_to_bv 64 (p_k0 p)) (Z_to_bv 64 (p_nu p)) a0 cnu c64 c16 c24 c60 cnn ctt s3 s5 hs7 hs9 t3 (Z_to_bv 64 (p_tp p)) (Z_to_bv 64 w) t6)
            F (Z_to_bv 64 0x85a24) fc None m (seg_rom b0segs)).
  (* [comment removed for export] *)
  Definition R2S (f : nat) (p : pst) : Prop :=
    forall (a0 s3 s5 t4 : word) (w : Z) (m : word -> option byte) (dbytes rest : list byte),
      CHf m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 2%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (1 <= p_nu p < PP)%Z ->
      (0 <= w < 4294967296)%Z -> p_tp p = (w / 256)%Z -> (1 <= p_rn p)%Z ->
      evt b0segs (KQ (PG2b (Datatypes.S f) PP (Z.lxor (Z.land w 255) (rmask (p_rn p))) (DR p (p_rn p - 1)) (Ss p)))
        (MS (B0RR c SHS cm4 cpp (Z_to_bv 64 (p_k0 p)) cntt a0 cnu c64 c16 c24 c60 cnn ctt s3 s5 hs7 hs9 (Z_to_bv 64 (p_nu p)) t4 (Z_to_bv 64 (p_tp p)) (Z_to_bv 64 w))
            F (Z_to_bv 64 0x85b78) fc None m (seg_rom b0segs)).
  (* [comment removed for export] *)
  Definition R3S (f : nat) (p : pst) : Prop :=
    forall (ra a0 s3 s5 t3 : word) (w : Z) (m : word -> option byte) (dbytes rest : list byte),
      CHf m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f - 1)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 3%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (2 <= p_nu p < PP)%Z ->
      (0 <= w < 4294967296)%Z -> p_tp p = (w / 256)%Z -> (1 <= p_rn p)%Z ->
      evt b0segs (KQ (PG3b (Datatypes.S f) PP (Z.lxor (Z.land w 255) (rmask (p_rn p))) (DR p (p_rn p - 1)) (Ss p)))
        (MS (B0RR c SHS ra cpp (Z_to_bv 64 (p_k0 p)) cntt a0 cnu c64 c16 c24 c60 cnn ctt s3 s5 hs7 hs9 t3 (Z_to_bv 64 (p_nu p)) (Z_to_bv 64 w) (Z_to_bv 64 (p_tp p)))
            F (Z_to_bv 64 0x85cc0) fc None m (seg_rom b0segs)).
  (* [comment removed for export] *)
  Definition R4S (f : nat) (p : pst) : Prop :=
    forall (t0 a0 s3 s5 t5 t6 : word) (w : Z) (m : word -> option byte) (dbytes rest : list byte),
      CHf m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f - 2)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 3%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (3 <= p_nu p < PP)%Z ->
      (0 <= w < 4294967296)%Z -> p_tp p = (w / 256)%Z -> (1 <= p_rn p)%Z ->
      evt b0segs (KQ (PG4b (Datatypes.S f) (Z.lxor (Z.land w 255) (rmask (p_rn p))) (DR p (p_rn p - 1)) (Ss p)))
        (MS (B0RR c SHS cm4 t0 (Z_to_bv 64 w) cntt a0 cnu c64 c16 c24 c60 cnn ctt s3 s5 hs7 hs9 (Z_to_bv 64 (p_nu p)) (Z_to_bv 64 (p_tp p)) t5 t6)
            F (Z_to_bv 64 0x85e00) fc None m (seg_rom b0segs)).
  (* [comment removed for export] *)
  Definition R5S (f : nat) (p : pst) : Prop :=
    forall (ra t1 t2 a5 a6 a7 s3 s5 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CHf m p dbytes rest -> sinvR p -> (PP - p_nu p <= Z.of_nat f - 3)%Z -> (1 <= p_av p)%Z ->
      (4 <= p_ol p <= 259)%Z -> (0 <= p_k0 p < 256)%Z -> (4 <= p_nu p <= PP)%Z -> (p_tp p < 16777216)%Z -> (1 <= p_rn p)%Z ->
      evt b0segs (KQ (K_PM f (set8 d0 (p_oc p) (p_ol p) (p_nu p + 1) (Z.lxor (p_k0 p) (rmask (p_rn p))) (p_tp p) (p_rn p - 1) (p_rt p) (p_cb p)) (Ss p)))
        (MS (B0RR c SHS ra (Z_to_bv 64 (p_nu p)) t1 t2 (Z_to_bv 64 (S + 24)) cnu c64 (Z_to_bv 64 (p_k0 p)) c24 a5 a6 a7 s3 s5 hs7 hs9 t3 t4 t5 t6)
            F (Z_to_bv 64 0x85f58) fc None m (seg_rom b0segs)).
  Ltac pcut := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh].
  Ltac pcut_in H := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh] in H.
  Ltac pcut_all := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh] in *.
  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & TTA & CRC & RNA & GOT & MI); unfold FGOTA in GOT; b0img.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac unCH H := let DSm := fresh "DSm" in let DE := fresh "DE" in let ROm := fresh "ROm" in let FSL := ident:(FSL) in
    cps_destruct H as (DSm & DE & FSL & ROm & MU & WM); unDS DSm; cps_destruct DE as (DSTA & DL & Edb & Lout); unRO ROm;
    unfold FSLs, bzd_slots in FSL.
  Ltac unSH := let SHbf := ident:(SHbf) in let SH' := fresh "SH" in pose proof SH as SH';
    cps_destruct SH' as (SHs & SHt & SHd & SHc & SHr & SHbf & _); b0img;
    let OKF' := fresh "OKF" in pose proof OKF as OKF'; specialize (SHbf (proj1 OKF')); clear OKF'.
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let ALS := ident:(ALS) in let ALM := ident:(ALM) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & HSP & (ALS & ALM) & SEP_SM & SEP_SD & SEP_MD & IAS & IAM & IAD & HIHI & JWF & ENT);
    let OKF' := fresh "OKF" in pose proof OKF as OKF';
    cps_destruct OKF' as (HSM & HTT & SEP_ST & SEP_MT & SEP_DT & IAT);
    destruct (zmod16_lin _ ALS) as [qS EqS]; destruct (zmod8_lin _ ALM) as [qSTRM EqSTRM]; destruct (zmod4_lin _ ALT) as [qTT EqTT];
    clear ALS ALM;
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & _ & Rtt & _ & _);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold disj, bzd_img_apart in *;
    unfold FWBA, FWB in *; cbn [app] in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length (d_tt d0) cap ltac:(lia)) as TTL; pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL;
    pose proof (proj2 ANS : saddr S SHS) as ANS0;
    hide_disj.
  Ltac ro_close := unfold FROfA, FGOTA; b0img; repeat match goal with |- _ /\ _ => split end; assumption.
  Ltac dsg_close := let HD := ident:(HD) in let NBU := ident:(NBU) in let MID := ident:(MID) in let SM := ident:(SM) in
    unfold DSgA; b0img; focbn; repeat match goal with |- _ /\ _ => split end; [exact_cells HD | exact_cells NBU | exact_cells MID | exact_cells SM].
  Ltac destg_close := unfold DESTgA; b0img; focbn; repeat match goal with |- _ /\ _ => split end; first [eassumption | cbn [length]; lia].
  Ltac fsl_close := let FSL := ident:(FSL) in first [ exact FSL | unfold bzd_slots; exact FSL | unfold FSLs, bzd_slots; exact FSL ].
  Ltac ch_close MU WM := repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM].
  Ltac unhide_k0 := try match goal with H : id ((0 <= _ < 256)%Z \/ _) |- _ => unfold id in H end.
  Ltac sinv_close := unfold S0F_bzd_sr1.sinvR; pcut;
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  Ltac sbl := wstep; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => rewrite ?le1_sx32_lit, ?BzInv.le1_lit; mem_after_store end.
  Ltac exitK MU WM := eapply KE; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia].
  Ltac joinK MU WM := eapply KJ; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM | ];
    unfold ojoin; focbn; unhide_k0; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lia | intros; lia | idtac].
  Ltac open_cut :=
    unfold CHf, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_sr1.sinvR in *; pcut_all.
  (* [comment removed for export] *)
  Ltac tt_load pc i :=
    brun_to pc;
    lazymatch goal with TTA : u32arr _ ?mm TT _ |- _ =>
      let RD := fresh "RD" in
      pose proof (zw32_read b0segs mm TT (d_tt d0) cap i _ TTA ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD; wstep; clear RD end.
  (* [comment removed for export] *)
  Ltac rn_load pc i :=
    brun_to pc;
    lazymatch goal with RNA : u32arr _ ?mm 858432 rnums_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read b0segs mm 858432 rnums_words i (Z_to_bv 64 (rNums i)) _ RNA (rnums_words_nth i ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; rewrite ?(sx32_of_Z (rNums i)) by lia end.
  (* [comment removed for export] *)
  Ltac nbu_fix v := match goal with H : rw_cells _ _ (_ + 1092)%Z [C4 (Z_to_bv 64 ?e)] |- _ => replace e with v in H by lia end.
End FR.
End ACeilS1.
