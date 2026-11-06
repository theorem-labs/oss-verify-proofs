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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzWalkArith BzWalkArith2 S0_bzd_out BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDOKS DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out S0F_bzd_outS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_snr1.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit DecCutA A0F_decV A0F_bzdV.
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
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section SNR.
  Variable c : foctx.
  Variable SHS : Z. Variable w0 w32 : word.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation L16 := (b_ll16 (o_cx c)). Notation L4 := (b_ll4 (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation cf := (d_cftab (o_d c)).
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation uspi := (bv_unsigned (o_SP c)).
  Notation RO := (FROsA DI_A0 c). Notation WB := (FWBA c).
  (* [comment removed for export] *)
  Notation SRR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 :=
    (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (b_s (o_cx c))) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (b_s (o_cx c) + 16)) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (b_s (o_cx c) + 1096))
         (Z_to_bv 64 (b_s (o_cx c) + 3152)) t3 t4 t5 t6) (only parsing).
  Hypothesis OK : foctx_okA c AIHI0. Hypothesis OKS : foctx_okSA c AIHI0.
  Hypothesis ANS : sanchor S SHS.
  Hypothesis SH : obz_sh DI_A0 c WB m0.
  Hypothesis KJ : A0_FKjoin c SHS w0 (FROsA DI_A0 c).
  Hypothesis KE : A0_FKexit c SHS w0 (FROsA DI_A0 c).

  (* [comment removed for export] *)
  Notation pst := S0F_bzd_snr1.pst. Notation PST := S0F_bzd_snr1.PST.
  Notation p_oc := S0F_bzd_snr1.p_oc. Notation p_ol := S0F_bzd_snr1.p_ol. Notation p_nu := S0F_bzd_snr1.p_nu. Notation p_k0 := S0F_bzd_snr1.p_k0.
  Notation p_tp := S0F_bzd_snr1.p_tp. Notation p_rn := S0F_bzd_snr1.p_rn. Notation p_rt := S0F_bzd_snr1.p_rt. Notation p_cb := S0F_bzd_snr1.p_cb.
  Notation p_out := S0F_bzd_snr1.p_out. Notation p_av := S0F_bzd_snr1.p_av. Notation p_tout := S0F_bzd_snr1.p_tout.
  Notation p_tol := S0F_bzd_snr1.p_tol. Notation p_toh := S0F_bzd_snr1.p_toh.
  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation sinv := (S0F_bzd_snr1.sinv c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation csnb := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)))).
  Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)).
  Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).
  (* [comment removed for export] *)
  Notation cra := (Z_to_bv 64 (SHS + 398)).           (* [comment removed for export] *)
  Notation ct1 := (Z_to_bv 64 (SHS + -2147450879)).   (* [comment removed for export] *)
  Notation ca7 := (Z_to_bv 64 (SHS + -2147450878)).   (* [comment removed for export] *)
  Notation csh := (Z_to_bv 64 SHS).                   (* [comment removed for export] *)
  Notation cs6 := (Z_to_bv 64 (b_s (o_cx c) + 12)). Notation cs8 := (Z_to_bv 64 (b_s (o_cx c) + 3184)).
  Notation c16 := (Z_to_bv 64 (SHS + 2)).             (* [comment removed for export] *)
  Notation c60 := (Z_to_bv 64 (SHS + 7)).             (* [comment removed for export] *)
  Notation c64 := (Z_to_bv 64 (SHS + 8)).             (* [comment removed for export] *)
  Notation cnu := (Z_to_bv 64 (SHS + 136)).           (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition FSLs (m : word -> option byte) : Prop :=
    rw_cells a0segs m uspi
      (bzd_slots S SHS w0 w32 (Z_to_bv 64 (SHS + -2147450484)) (Z_to_bv 64 (SHS + -2147450485)) (Z_to_bv 64 (SHS + -2147450877))
                 (Z_to_bv 64 (SHS + -2147450878)) (Z_to_bv 64 (SHS + -2147450872)) (Z_to_bv 64 (SHS + -2147450873))
                 (Z_to_bv 64 (SHS + -2147450875)) (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870))).

  (* [comment removed for export] *)
  Definition CH (m : word -> option byte) (p : pst) (dbytes rest : list byte) : Prop :=
    DSgA DI_A0 c m (Jp p) (D p) (Ss p) /\ DESTgA DI_A0 c m (Ss p) dbytes rest /\ FSLs m /\ RO m /\ munch WB m0 m /\ wmono a0segs m0 m.

  (* [comment removed for export] *)
  Definition MS_ (f : nat) (p : pst) : Prop :=
    forall (t0 t2 a2 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinv p -> (PP - p_nu p <= Z.of_nat f)%Z ->
      evt a0segs (KQ (K_PM f (D p) (Ss p)))
        (MS (SRR cra t0 ct1 t2 (Z_to_bv 64 (p_av p)) cstrm a2 a3 a4 a5 a6 ca7 s3 s4 csh cs6 s7 cs8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x85c1c) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition TLS (f : nat) (p : pst) : Prop :=
    forall (t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinv p -> (PP - p_nu p <= Z.of_nat f)%Z ->
      evt a0segs (KQ (K_PM f (D p) (Ss p)))
        (MS (SRR cra t0 ct1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x856a0) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition HS (f : nat) (p : pst) : Prop :=
    forall (t0 t2 a0 a2 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinv p -> (PP - p_nu p <= Z.of_nat f)%Z -> (1 <= p_av p)%Z ->
      evt a0segs (KQ (K_PH f (D p) (Ss p)))
        (MS (SRR cra t0 ct1 t2 a0 cstrm a2 a3 a4 a5 a6 ca7 s3 s4 csh cs6 s7 cs8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x85c24) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition OUTS (f : nat) (p : pst) : Prop :=
    forall (t0 t2 a0 a2 a3 a4 a6 s3 s4 s7 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinv p -> (PP - p_nu p <= Z.of_nat f)%Z -> (1 <= p_av p)%Z -> (1 <= p_ol p)%Z ->
      evt a0segs (KQ (K_PH f (D p) (Ss p)))
        (MS (SRR cra t0 ct1 t2 a0 cstrm a2 a3 a4 c16 a6 ca7 s3 s4 csh cs6 s7 cs8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x85c38) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition GS (f : nat) (p : pst) : Prop :=
    forall (t0 t2 a0 a1 a2 a3 a4 a6 s3 s4 s7 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinv p -> (PP - p_nu p <= Z.of_nat f)%Z -> (1 <= p_av p)%Z -> p_ol p = 0%Z ->
      evt a0segs (KQ (K_PG f (D p) (Ss p)))
        (MS (SRR cra t0 ct1 t2 a0 a1 a2 a3 a4 c16 a6 ca7 s3 s4 csh cs6 s7 cs8 t3 t4 t5 t6)
            F (Z_to_bv 64 0x85df8) fc None m (seg_rom a0segs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition T1S (f' : nat) (p : pst) : Prop :=
    forall (t0 a0 a1 a2 s3 s6 s8 t3 t4 : word) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinv p -> (PP - p_nu p <= Z.of_nat f' + 1)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 1%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (p_nu p < PP)%Z -> (p_tp p < cap)%Z ->
      evt a0segs (KQ (PG1 (Datatypes.S f') PP (D p) (Ss p)))
        (MS (SRR cra t0 ct1 cnn a0 a1 a2 cnu (Z_to_bv 64 (p_nu p)) c16 c60 c64 s3 (Z_to_bv 64 (p_tp p))
                 (Z_to_bv 64 (indexIntoF (p_tp p) cf)) s6 cm4 s8 t3 t4 csnb (Z_to_bv 64 (p_k0 p)))
            F (Z_to_bv 64 0x854ec) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition T2S (f' : nat) (p : pst) : Prop :=
    forall (a0 a1 s5 s6 t3 : word) (v16 : Z) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinv p -> (PP - p_nu p <= Z.of_nat f')%Z -> (1 <= p_av p)%Z ->
      p_ol p = 2%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (1 <= p_nu p < PP)%Z -> (p_tp p < cap)%Z ->
      (0 <= v16 < 65536)%Z -> Z.land (v16 * 4) 4 = Z.land (p_tp p * 4) 4 ->
      evt a0segs (KQ (PG2 (Datatypes.S f') PP (D p) (Ss p)))
        (MS (SRR cra cl16 ct1 cnn a0 a1 (Z_to_bv 64 (p_tp p)) cnu (Z_to_bv 64 (p_nu p - 1)) c16 c60 c64 (Z_to_bv 64 v16) (Z_to_bv 64 (p_nu p))
                 s5 s6 cm4 (Z_to_bv 64 (indexIntoF (p_tp p) cf)) t3 cl4 csnb (Z_to_bv 64 (p_k0 p)))
            F (Z_to_bv 64 0x85628) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition T3S (f' : nat) (p : pst) : Prop :=
    forall (a0 a1 s3 s8 t3 : word) (v16 : Z) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinv p -> (PP - p_nu p <= Z.of_nat f' - 1)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 3%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (2 <= p_nu p < PP)%Z -> (p_tp p < cap)%Z ->
      (0 <= v16 < 65536)%Z -> Z.land (v16 * 4) 4 = Z.land (p_tp p * 4) 4 ->
      evt a0segs (KQ (PG3 (Datatypes.S f') PP (D p) (Ss p)))
        (MS (SRR cra cl16 ct1 cnn a0 a1 (Z_to_bv 64 (p_tp p)) cnu (Z_to_bv 64 (p_nu p - 2)) c16 c60 c64 s3 (Z_to_bv 64 (indexIntoF (p_tp p) cf))
                 (Z_to_bv 64 v16) (Z_to_bv 64 (p_nu p)) cm4 s8 t3 cl4 csnb (Z_to_bv 64 (p_k0 p)))
            F (Z_to_bv 64 0x85770) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition T4S (f' : nat) (p : pst) : Prop :=
    forall (a0 a1 s4 s5 s6 s8 t3 t5 : word) (v16 : Z) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinv p -> (PP - p_nu p <= Z.of_nat f' - 2)%Z -> (1 <= p_av p)%Z ->
      p_ol p = 3%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (3 <= p_nu p < PP)%Z -> (p_tp p < cap)%Z ->
      (0 <= v16 < 65536)%Z -> Z.land (v16 * 4) 4 = Z.land (p_tp p * 4) 4 ->
      evt a0segs (KQ (PG4 (Datatypes.S f') (D p) (Ss p)))
        (MS (SRR cra cl16 ct1 cnn a0 a1 (Z_to_bv 64 (p_tp p)) cnu (Z_to_bv 64 (p_nu p - 3)) c16 c60 c64 (Z_to_bv 64 v16) s4 s5 s6 cm4 s8 t3 cl4 t5
                 (Z_to_bv 64 (indexIntoF (p_tp p) cf)))
            F (Z_to_bv 64 0x8586c) fc None m (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition T5S (f' : nat) (p : pst) : Prop :=
    forall (t2 a0 a5 s3 s4 s5 s6 s7 s8 t3 t6 : word) (v16 : Z) (m : word -> option byte) (dbytes rest : list byte),
      CH m p dbytes rest -> sinv p -> (PP - p_nu p <= Z.of_nat f' - 3)%Z -> (1 <= p_av p)%Z ->
      (4 <= p_ol p <= 259)%Z -> p_oc p = p_k0 p -> (0 <= p_k0 p < 256)%Z -> (4 <= p_nu p <= PP)%Z -> (p_tp p < cap)%Z ->
      (0 <= v16 < 65536)%Z -> Z.land (v16 * 4) 4 = Z.land (p_tp p * 4) 4 ->
      evt a0segs (KQ (PG5 (Datatypes.S f') (D p) (Ss p)))
        (MS (SRR cra cl16 ct1 t2 a0 (Z_to_bv 64 (p_tp p)) (Z_to_bv 64 (indexIntoF (p_tp p) cf)) cnu (Z_to_bv 64 (p_nu p - 4)) a5 c60 c64
                 s3 s4 s5 s6 s7 s8 t3 cl4 (Z_to_bv 64 v16) t6)
            F (Z_to_bv 64 0x85958) fc None m (seg_rom a0segs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & L16A & L4A & CFA & CRC & RNA & GOT & MI); unfold FGOTA in GOT; a0img.
  Ltac unSH := let SHbs := ident:(SHbs) in let SH' := fresh "SH" in pose proof SH as SH';
    cps_destruct SH' as (SHs & SHt & SHd & SHc & SHr & _ & SHbs); a0img;
    let OKS' := fresh "OKS" in pose proof OKS as OKS'; specialize (SHbs (proj1 OKS')); clear OKS';
    cps_destruct SHbs as (SH16 & SH4).
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & HSP & HAL & SEP_SM & SEP_SD & SEP_MD & IAS & IAM & IAD & HIHI & JWF & ENT);
    let OKS' := fresh "OKS" in pose proof OKS as OKS';
    cps_destruct OKS' as (HSM & HL16 & HL4 & SEP_S16 & SEP_M16 & SEP_D16 & SEP_S4 & SEP_M4 & SEP_D4 & SEP_164 & IA16 & IA4);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & Rcf & Rtt & Rl16 & Rl4);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold disj, bzd_img_apart in *;
    unfold FWBA, FWB in *; cbn [app] in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length cf 257 ltac:(lia)) as CFL;
    pose proof (zh16_length (d_ll16 d0) (200000 * n) ltac:(lia)) as L16L; pose proof (zb8_length (d_ll4 d0) (50000 * n) ltac:(lia)) as L4L;
    pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL;
    pose proof (proj2 ANS : saddr S SHS) as ANS0;
    hide_disj.

  (* [comment removed for export] *)
  Ltac cf_load pclw i :=
    lazymatch goal with CFA : u32arr _ ?mm (S + 1096)%Z _, Rcf : _ -> forall i0 : Z, _ |- _ =>
      let RD := fresh "RD" in let CR := fresh "CFR" in
      pose proof (Rcf ltac:(lia) i ltac:(lia)) as CR;
      pose proof (zw32_read a0segs mm (S + 1096)%Z cf 257 i _ CFA ltac:(lia) eq_refl) as RD;
      arun_to pclw; wstep; clear RD; try rewrite (sx32_of_Z (zget cf i)) by lia end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma snr_B1 : forall (P : machine_state -> Prop) (m : word -> option byte) (idx : Z)
      (ra t1 t2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 t5 t6 : word),
    RO m -> munch WB m0 m -> (0 <= idx < 2147483648)%Z ->
    (forall (a0 a1 t3 t4 : word) (lo hi : Z), iif_state (zget cf) idx 8 = (lo, hi) ->
       evt a0segs P (MS (SRR ra (Z_to_bv 64 hi) t1 t2 a0 a1 (Z_to_bv 64 idx) a3 a4 a5 a6 a7 s3 s4 (Z_to_bv 64 lo) s6 s7 s8 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x854ec) fc None m (seg_rom a0segs))) ->
    forall (k t : nat) (lo hi : Z) (a0 a1 t3 t4 : word), (t + k = 7)%nat -> iif_state (zget cf) idx t = (lo, hi) ->
      evt a0segs P (MS (SRR ra (Z_to_bv 64 hi) t1 t2 a0 a1 (Z_to_bv 64 idx) a3 a4 a5 a6 a7 s3 s4 (Z_to_bv 64 lo) s6 s7 s8 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x8549c) fc None m (seg_rom a0segs)).
  Proof.
    intros P m idx. intros until t6. intros ROm MU Hidx EXIT k.
    induction k as [|k IH]; intros t lo hi a0 a1 t3 t4 Hk E; unRO ROm; prep; unSH;
      pose proof (iif_stepW (zget cf) idx t lo hi ltac:(lia) E) as SW; cbv zeta in SW;
      cps_destruct SW as (A & B & Cm & Dh & E1 & XT).
    - (* [comment removed for export] *)
      assert (Ht7 : t = 7%nat) by lia. subst t.
      wstep. wstep. wstep. wstep. cf_load 0x854bc%Z ((lo + hi) / 2)%Z.
      wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + (* [comment removed for export] *)
        replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. wstep. wstep. if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        wstep. eapply EXIT. exact E1.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        wstep. eapply EXIT. exact E1.
    - wstep. wstep. wstep. wstep. cf_load 0x854bc%Z ((lo + hi) / 2)%Z.
      wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. wstep. wstep. if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
  Time Qed.

  (* [comment removed for export] *)
  Lemma snr_B2 : forall (P : machine_state -> Prop) (m : word -> option byte) (idx : Z)
      (ra t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s7 t4 t5 t6 : word),
    RO m -> munch WB m0 m -> (0 <= idx < 2147483648)%Z ->
    (forall (a0 a1 t3 s6 : word) (lo hi : Z), iif_state (zget cf) idx 8 = (lo, hi) ->
       evt a0segs P (MS (SRR ra t0 t1 t2 a0 a1 (Z_to_bv 64 idx) a3 a4 a5 a6 a7 s3 s4 (Z_to_bv 64 hi) s6 s7 (Z_to_bv 64 lo) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x85628) fc None m (seg_rom a0segs))) ->
    forall (k t : nat) (lo hi : Z) (a0 a1 t3 s6 : word), (t + k = 7)%nat -> iif_state (zget cf) idx t = (lo, hi) ->
      evt a0segs P (MS (SRR ra t0 t1 t2 a0 a1 (Z_to_bv 64 idx) a3 a4 a5 a6 a7 s3 s4 (Z_to_bv 64 hi) s6 s7 (Z_to_bv 64 lo) t3 t4 t5 t6)
                      F (Z_to_bv 64 0x855c4) fc None m (seg_rom a0segs)).
  Proof.
    intros P m idx. intros until t6. intros ROm MU Hidx EXIT k.
    induction k as [|k IH]; intros t lo hi a0 a1 t3 s6 Hk E; unRO ROm; prep; unSH;
      pose proof (iif_stepW (zget cf) idx t lo hi ltac:(lia) E) as SW; cbv zeta in SW;
      cps_destruct SW as (A & B & Cm & Dh & E1 & XT).
    - (* [comment removed for export] *)
      assert (Ht7 : t = 7%nat) by lia. subst t.
      wstep. wstep. wstep. wstep. cf_load 0x855e4%Z ((lo + hi) / 2)%Z.
      wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + (* [comment removed for export] *)
        replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. wstep. wstep. if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        wstep. eapply EXIT. exact E1.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        wstep. eapply EXIT. exact E1.
    - wstep. wstep. wstep. wstep. cf_load 0x855e4%Z ((lo + hi) / 2)%Z.
      wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. wstep. wstep. if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
  Time Qed.

  (* [comment removed for export] *)
  Lemma snr_B3 : forall (P : machine_state -> Prop) (m : word -> option byte) (idx : Z)
      (ra t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 t4 t5 t6 : word),
    RO m -> munch WB m0 m -> (0 <= idx < 2147483648)%Z ->
    (forall (a0 a1 t3 s8 : word) (lo hi : Z), iif_state (zget cf) idx 8 = (lo, hi) ->
       evt a0segs P (MS (SRR ra t0 t1 t2 a0 a1 (Z_to_bv 64 idx) a3 a4 a5 a6 a7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) s5 s6 s7 s8 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x85770) fc None m (seg_rom a0segs))) ->
    forall (k t : nat) (lo hi : Z) (a0 a1 t3 s8 : word), (t + k = 7)%nat -> iif_state (zget cf) idx t = (lo, hi) ->
      evt a0segs P (MS (SRR ra t0 t1 t2 a0 a1 (Z_to_bv 64 idx) a3 a4 a5 a6 a7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) s5 s6 s7 s8 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x85704) fc None m (seg_rom a0segs)).
  Proof.
    intros P m idx. intros until t6. intros ROm MU Hidx EXIT k.
    induction k as [|k IH]; intros t lo hi a0 a1 t3 s8 Hk E; unRO ROm; prep; unSH;
      pose proof (iif_stepW (zget cf) idx t lo hi ltac:(lia) E) as SW; cbv zeta in SW;
      cps_destruct SW as (A & B & Cm & Dh & E1 & XT).
    - (* [comment removed for export] *)
      assert (Ht7 : t = 7%nat) by lia. subst t.
      wstep. wstep. wstep. wstep. cf_load 0x85724%Z ((lo + hi) / 2)%Z.
      wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + (* [comment removed for export] *)
        replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. wstep. wstep. if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        wstep. eapply EXIT. exact E1.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        wstep. eapply EXIT. exact E1.
    - wstep. wstep. wstep. wstep. cf_load 0x85724%Z ((lo + hi) / 2)%Z.
      wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. wstep. wstep. if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
  Time Qed.

  (* [comment removed for export] *)
  Lemma snr_B4 : forall (P : machine_state -> Prop) (m : word -> option byte) (idx : Z)
      (ra t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 t4 : word),
    RO m -> munch WB m0 m -> (0 <= idx < 2147483648)%Z ->
    (forall (a0 a1 t3 s4 : word) (lo hi : Z), iif_state (zget cf) idx 8 = (lo, hi) ->
       evt a0segs P (MS (SRR ra t0 t1 t2 a0 a1 (Z_to_bv 64 idx) a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 (Z_to_bv 64 hi) (Z_to_bv 64 lo))
                       F (Z_to_bv 64 0x8586c) fc None m (seg_rom a0segs))) ->
    forall (k t : nat) (lo hi : Z) (a0 a1 t3 s4 : word), (t + k = 7)%nat -> iif_state (zget cf) idx t = (lo, hi) ->
      evt a0segs P (MS (SRR ra t0 t1 t2 a0 a1 (Z_to_bv 64 idx) a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 (Z_to_bv 64 hi) (Z_to_bv 64 lo))
                      F (Z_to_bv 64 0x85800) fc None m (seg_rom a0segs)).
  Proof.
    intros P m idx. intros until t4. intros ROm MU Hidx EXIT k.
    induction k as [|k IH]; intros t lo hi a0 a1 t3 s4 Hk E; unRO ROm; prep; unSH;
      pose proof (iif_stepW (zget cf) idx t lo hi ltac:(lia) E) as SW; cbv zeta in SW;
      cps_destruct SW as (A & B & Cm & Dh & E1 & XT).
    - (* [comment removed for export] *)
      assert (Ht7 : t = 7%nat) by lia. subst t.
      wstep. wstep. wstep. wstep. cf_load 0x85820%Z ((lo + hi) / 2)%Z.
      wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + (* [comment removed for export] *)
        replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. wstep. wstep. if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        wstep. eapply EXIT. exact E1.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        wstep. eapply EXIT. exact E1.
    - wstep. wstep. wstep. wstep. cf_load 0x85820%Z ((lo + hi) / 2)%Z.
      wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. wstep. wstep. if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
  Time Qed.

  (* [comment removed for export] *)
  Lemma snr_B5 : forall (P : machine_state -> Prop) (m : word -> option byte) (idx : Z)
      (ra t0 t1 a3 a4 a6 a7 s3 s4 s5 s6 s7 s8 t4 t5 t6 : word),
    RO m -> munch WB m0 m -> (0 <= idx < 2147483648)%Z ->
    (forall (a0 t2 t3 : word) (lo hi : Z), iif_state (zget cf) idx 8 = (lo, hi) ->
       evt a0segs P (MS (SRR ra t0 t1 t2 a0 (Z_to_bv 64 idx) (Z_to_bv 64 lo) a3 a4 (Z_to_bv 64 hi) a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x85958) fc None m (seg_rom a0segs))) ->
    forall (k t : nat) (lo hi : Z) (a0 t2 t3 : word), (t + k = 7)%nat -> iif_state (zget cf) idx t = (lo, hi) ->
      evt a0segs P (MS (SRR ra t0 t1 t2 a0 (Z_to_bv 64 idx) (Z_to_bv 64 lo) a3 a4 (Z_to_bv 64 hi) a6 a7 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x85908) fc None m (seg_rom a0segs)).
  Proof.
    intros P m idx. intros until t6. intros ROm MU Hidx EXIT k.
    induction k as [|k IH]; intros t lo hi a0 t2 t3 Hk E; unRO ROm; prep; unSH;
      pose proof (iif_stepW (zget cf) idx t lo hi ltac:(lia) E) as SW; cbv zeta in SW;
      cps_destruct SW as (A & B & Cm & Dh & E1 & XT).
    - (* [comment removed for export] *)
      assert (Ht7 : t = 7%nat) by lia. subst t.
      wstep. wstep. wstep. wstep. cf_load 0x85928%Z ((lo + hi) / 2)%Z.
      wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + (* [comment removed for export] *)
        replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. wstep. wstep. if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        wstep. eapply EXIT. exact E1.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2; [exfalso; apply K2; apply (proj2 XT); lia|].
        wstep. eapply EXIT. exact E1.
    - wstep. wstep. wstep. wstep. cf_load 0x85928%Z ((lo + hi) / 2)%Z.
      wstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
      + replace (zget cf ((lo + hi) / 2) <=? idx) with false in E1, XT by (symmetry; apply Z.leb_gt; lia).
        wstep. wstep. wstep. if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
      + replace (zget cf ((lo + hi) / 2) <=? idx) with true in E1, XT by (symmetry; apply Z.leb_le; lia).
        wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2; [| exfalso; assert (t = 7%nat) by (apply (proj1 XT); lia); lia].
        eapply (IH (Datatypes.S t)); [lia| exact E1].
  Time Qed.

End SNR.
End ACeilS1.
