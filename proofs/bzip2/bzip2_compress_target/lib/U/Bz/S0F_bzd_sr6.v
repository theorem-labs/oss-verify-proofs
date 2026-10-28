(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_out S0F_bzd_outS S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_outR S0F_bzd_snr1 S0F_bzd_sr1.
From Stdlib Require Lia. 
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require UKit U0_idx.
Module S0F_bzd_sr3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Arith.Wf_nat.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_outS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_fr1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_fr2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_outR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_snr1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_sr1.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

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
  Hypothesis OK : foctx_ok c. Hypothesis OKS : foctx_okS c. Hypothesis RD1 : d_rand (o_d c) = 1%Z.
  Hypothesis KJ : FKjoin c (FROs c).
  Hypothesis KE : FKexit c (FROs c).
  Hypothesis AL : foctx_al c.

  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation CH := (S0F_bzd_snr1.CH c). Notation sinvR := (S0F_bzd_sr1.sinvR c). Notation DR := (S0F_bzd_sr1.DR c).
  Notation MS_ := (S0F_bzd_sr1.MS_ c). Notation HS := (S0F_bzd_sr1.HS c). Notation OUTS := (S0F_bzd_sr1.OUTS c).
  Notation GS := (S0F_bzd_sr1.GS c).
  Notation T1S := (S0F_bzd_sr1.T1S c). Notation T2S := (S0F_bzd_sr1.T2S c). Notation T3S := (S0F_bzd_sr1.T3S c).
  Notation T4S := (S0F_bzd_sr1.T4S c). Notation T5S := (S0F_bzd_sr1.T5S c).
  Notation R1S := (S0F_bzd_sr1.R1S c). Notation R2S := (S0F_bzd_sr1.R2S c). Notation R3S := (S0F_bzd_sr1.R3S c).
  Notation R4S := (S0F_bzd_sr1.R4S c). Notation R5S := (S0F_bzd_sr1.R5S c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation cPP := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)) + 1)).
  Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)). Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).
  Notation nl16 := (Z_to_bv 64 (18446744073709551615 - b_ll16 (o_cx c))). Notation nl4 := (Z_to_bv 64 (18446744073709551615 - b_ll4 (o_cx c))).

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
  Ltac unAL := let AL' := fresh "AL" in pose proof AL as AL'; unfold foctx_al, ctx_al in AL'; cps_destruct AL' as ((ALs & ALsp & ALsrc & ALdst & ALtt & AL16 & AL4) & ALstrm).
  Ltac ro_close := unfold FROs, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.
  (* [comment removed for export] *)
  Ltac dsg_close := unfold DSg; focbn; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lazymatch goal with |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact_cells H end end].
  Ltac destg_close := unfold DESTg; focbn; repeat match goal with |- _ /\ _ => split end; first [eassumption | cbn [length]; lia].
  Ltac unhide_k0 := try match goal with H : id ((0 <= _ < 256)%Z \/ _) |- _ => unfold id in H end.
  Ltac sinv_close := unfold S0F_bzd_sr1.sinvR; cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh];
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  Ltac ojoin_close := unfold ojoin; focbn; unhide_k0; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lia | intros; lia | idtac].
  (* [comment removed for export] *)
  Ltac open_cut :=
    unfold S0F_bzd_snr1.CH, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_sr1.sinvR in *;
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in *.
  (* [comment removed for export] *)
  Ltac spec_cut G CUT rec nm :=
    pose proof (G rec) as nm; unfold CUT in nm;
    unfold S0F_bzd_snr1.CH, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in nm;
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in nm.
  (* [comment removed for export] *)
  Ltac l4_load i :=
    lazymatch goal with L4A : u8arr _ ?mm L4 _, R4 : forall i0 : Z, (0 <= zget (d_ll4 _) i0 < 256)%Z |- _ =>
      let RD := fresh "RD" in let R := fresh "Rv4" in
      pose proof (R4 i) as R;
      pose proof (zb8_read1 s0segs mm L4 (d_ll4 d0) (50000 * n) i _ L4A ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite zxb_lit8 by lia end.
  Ltac l16_load i :=
    lazymatch goal with L16A : u8arr _ ?mm L16 _, R16 : forall i0 : Z, (0 <= zget (d_ll16 _) i0 < 65536)%Z |- _ =>
      let RD := fresh "RD" in let R := fresh "Rv16" in
      pose proof (R16 i) as R;
      pose proof (zh16_read2 s0segs mm L16 (d_ll16 d0) (200000 * n) i _ L16A ltac:(lia) ltac:(lia) R eq_refl) as RD;
      wstep; clear RD; try rewrite (zx16_of_Z (zget (d_ll16 d0) i)) by lia end.
  Ltac name_sh tp sh :=
    let E := fresh "E" sh in let C := fresh "C" sh in
    remember (Z.land (tp * 4) 4) as sh eqn:E;
    pose proof (ll4_shift_cases tp) as C; rewrite <- E in C;
    let R := fresh "R" sh in assert (R : (0 <= sh <= 4)%Z) by lia; hide_disj.
  Ltac srlw_norm v4 sh :=
    rewrite (Z.mod_small sh 32) by lia; rewrite (swrap32_id (Z.shiftr v4 sh)) by lia;
    try rewrite (Z.mod_small (Z.shiftr v4 sh) 18446744073709551616) by lia.
  Ltac fold_ll v16 v4 tp sh Esh :=
    rewrite (shl60_shr44 (Z.shiftr v4 sh)) by (apply Z.shiftr_nonneg; lia);
    rewrite (lor_hi16 v16 (Z.shiftr v4 sh mod 16)) by (first [lia | apply Z.mod_pos_bound; lia]);
    replace (Z.shiftr v4 sh mod 16 * 65536 + v16)%Z with (llval v16 v4 tp) by (unfold llval; rewrite <- Esh; lia).
  Ltac nbu_fix v := match goal with H : rw_cells _ _ (_ + 1092)%Z [C4 (Z_to_bv 64 ?e)] |- _ => replace e with v in H by lia end.
  (* [comment removed for export] *)
  Ltac rn_load i :=
    lazymatch goal with RNA : u32arr _ ?mm 0x335b0 rnums_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read s0segs mm 0x335b0 rnums_words i (Z_to_bv 64 (rNums i)) _ RNA (rnums_words_nth i ltac:(lia)) ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite ?(sx32_of_Z (rNums i)) by lia end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_T1 : forall f', (forall p', R1S f' p') -> forall p, T1S f' p.
  Proof.
    intros f' IHR1 p. unfold S0F_bzd_sr1.T1S. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst ol oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unAL.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    pose proof (get_sym_SR (set8 d0 k0 1 nu k0 tp rn rt cb) ltac:(s8; unfold blk_cap; lia) ltac:(s8; rewrite Esm, HSM; lia) ltac:(s8; rewrite RD1; lia)) as GS1.
    rewrite gsSR_set8 in GS1.
    rewrite (PG1_b _ _ _ _ _ _ GS1). clear GS1.
    pose proof (Rl16 tp) as R16. pose proof (Rl4 (tp / 2)%Z) as R4.
    rewrite (get_ll_llval d0 tp) by lia.
    pose proof (indexIntoF_range tp cf) as KR. set (k1 := indexIntoF tp cf) in *.
    pose proof (rNn_range rn rt ltac:(lia) ltac:(lia)) as RN1. pose proof (rTn_range rn rt ltac:(lia)) as RT1.
    (* [comment removed for export] *)
    UKit.urun_to 0x14a5c%Z.
    (* [comment removed for export] *)
    l4_load (tp / 2)%Z. set (v4 := zget (d_ll4 d0) (tp / 2)) in *.
    l16_load tp. set (v16 := zget (d_ll16 d0) tp) in *.
    (* [comment removed for export] *)
    wstep. wstep. name_sh tp sh. pose proof (shiftr_byte v4 sh ltac:(lia) ltac:(lia)) as SR4.
    (* [comment removed for export] *)
    wstep. srlw_norm v4 sh. wstep. try rewrite (sx32_of_Z rn) by lia. wstep. wstep. wstep. fold_ll v16 v4 tp sh Esh.
    pose proof (llval_range v16 v4 tp ltac:(lia) ltac:(lia) ltac:(lia)) as TPR1. set (tp1 := llval v16 v4 tp) in *.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    wstep. if_cases K4; zify_cond K4.
    { rewrite (rNn_nz rn rt K4), (rTn_nz rn rt K4).
      spec_cut IHR1 S0F_bzd_sr1.R1S (PST k0 1 nu k0 tp1 rn rt cb out av tout tol toh) R1.
      enter_with (R1 _ _ _ _ _ _ _ k1 rn v16 _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close
        | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | subst tp1; symmetry; apply llval_bit2 ]. }
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z rt) by lia. UKit.urun_to 0x14ab8%Z.
    (* [comment removed for export] *)
    rn_load rt. pose proof (rNums_range rt ltac:(lia)) as RNR.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rewrite (rtpos_wrap rt) by lia.
    pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
    wstep. wstep.
    assert (Ez : rn = 0%Z) by lia. rewrite Ez. rewrite rNn_z, (rTn_z rt) by lia.
    spec_cut IHR1 S0F_bzd_sr1.R1S (PST k0 1 nu k0 tp1 (rNums rt) ((rt + 1) mod 512)%Z cb out av tout tol toh) R1.
    enter_with (R1 _ _ _ _ _ _ _ k1 (rNums rt) v16 _ dbytes rest);
      [ st_eq
      | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
      | sinv_close
      | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | subst tp1; symmetry; apply llval_bit2 ].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_R1 : forall f', (forall p', T2S f' p') -> (forall p', MS_ f' p') -> forall p, R1S f' p.
  Proof.
    intros f' IHT2 IHM p. unfold S0F_bzd_sr1.R1S. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp Hnb HrN1 Rv16p HSH.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst ol oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unAL.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    rewrite PG1b_eq. cbv zeta. s8.
    (* [comment removed for export] *)
    UKit.urun_to 0x14af4%Z. try nbu_fix (nu + 1)%Z.
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    { rewrite (proj2 (Z.eqb_eq (nu + 1) PP)) by lia.
      spec_cut IHM S0F_bzd_sr1.MS_ (PST k0 1 (nu + 1) k0 tp (rN1 - 1) rt cb out av tout tol toh) M.
      enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close | lia | lia ]. }
    rewrite (proj2 (Z.eqb_neq (nu + 1) PP)) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rewrite (mask_b2z rN1 HrN1). rewrite (land255_small nb) by lia.
    set (k1 := Z.lxor nb (rmask rN1)) in *.
    assert (Rk1 : (0 <= k1 < 256)%Z) by (subst k1; apply lxor_byte_bit; [lia | destruct (rN1 - 1 =? 1)%Z; lia]).
    (* [comment removed for export] *)
    wstep. if_cases K2; zify_cond K2.
    { rewrite (proj2 (Z.eqb_neq k1 k0)) by lia. cbn [negb].
      (* [comment removed for export] *)
      wstep.
      spec_cut IHM S0F_bzd_sr1.MS_ (PST k0 1 (nu + 1) k1 tp (rN1 - 1) rt cb out av tout tol toh) M.
      enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close | lia | lia ]. }
    rewrite (proj2 (Z.eqb_eq k1 k0)) by lia. cbn [negb]. s8.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    wstep. if_cases K3; zify_cond K3.
    2:{ rewrite PG2_None by (apply get_sym_None; s8; unfold blk_cap; lia).
      wstep.
      eapply KE; [dsg_close | destg_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia]. }
    (* [comment removed for export] *)
    wstep. wstep.
    lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mm _) =>
      eapply (S0F_bzd_sr1.sr_B2 c OK OKS P mm tp) with (k := 7%nat) (t := 0%nat); [ro_close | lia | | reflexivity | reflexivity] end.
    intros a7' s8' t3' t5' lo hi E8.
    pose proof (iif_result cf tp lo hi E8) as RES.
    spec_cut IHT2 S0F_bzd_sr1.T2S (PST k0 2 (nu + 1) k0 tp (rN1 - 1) rt cb out av tout tol toh) T2.
    rewrite <- RES.
    enter_with (T2 _ _ _ _ _ _ _ v16 _ dbytes rest);
      [ st_eq
      | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
      | sinv_close
      | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | exact HSH ].
  Time Qed.
End SR.
End ACeilS1.
End S0F_bzd_sr3.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
Module S0F_bzd_sr4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Arith.Wf_nat.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_outS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_fr1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_fr2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_outR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_snr1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_sr1.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

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
  Hypothesis OK : foctx_ok c. Hypothesis OKS : foctx_okS c. Hypothesis RD1 : d_rand (o_d c) = 1%Z.
  Hypothesis KJ : FKjoin c (FROs c).
  Hypothesis KE : FKexit c (FROs c).
  Hypothesis AL : foctx_al c.

  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation CH := (S0F_bzd_snr1.CH c). Notation sinvR := (S0F_bzd_sr1.sinvR c). Notation DR := (S0F_bzd_sr1.DR c).
  Notation MS_ := (S0F_bzd_sr1.MS_ c). Notation HS := (S0F_bzd_sr1.HS c). Notation OUTS := (S0F_bzd_sr1.OUTS c).
  Notation GS := (S0F_bzd_sr1.GS c).
  Notation T1S := (S0F_bzd_sr1.T1S c). Notation T2S := (S0F_bzd_sr1.T2S c). Notation T3S := (S0F_bzd_sr1.T3S c).
  Notation T4S := (S0F_bzd_sr1.T4S c). Notation T5S := (S0F_bzd_sr1.T5S c).
  Notation R1S := (S0F_bzd_sr1.R1S c). Notation R2S := (S0F_bzd_sr1.R2S c). Notation R3S := (S0F_bzd_sr1.R3S c).
  Notation R4S := (S0F_bzd_sr1.R4S c). Notation R5S := (S0F_bzd_sr1.R5S c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation cPP := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)) + 1)).
  Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)). Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).
  Notation nl16 := (Z_to_bv 64 (18446744073709551615 - b_ll16 (o_cx c))). Notation nl4 := (Z_to_bv 64 (18446744073709551615 - b_ll4 (o_cx c))).

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
  Ltac unAL := let AL' := fresh "AL" in pose proof AL as AL'; unfold foctx_al, ctx_al in AL'; cps_destruct AL' as ((ALs & ALsp & ALsrc & ALdst & ALtt & AL16 & AL4) & ALstrm).
  Ltac ro_close := unfold FROs, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.
  (* [comment removed for export] *)
  Ltac dsg_close := unfold DSg; focbn; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lazymatch goal with |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact_cells H end end].
  Ltac destg_close := unfold DESTg; focbn; repeat match goal with |- _ /\ _ => split end; first [eassumption | cbn [length]; lia].
  Ltac unhide_k0 := try match goal with H : id ((0 <= _ < 256)%Z \/ _) |- _ => unfold id in H end.
  Ltac sinv_close := unfold S0F_bzd_sr1.sinvR; cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh];
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  Ltac ojoin_close := unfold ojoin; focbn; unhide_k0; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lia | intros; lia | idtac].
  (* [comment removed for export] *)
  Ltac open_cut :=
    unfold S0F_bzd_snr1.CH, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_sr1.sinvR in *;
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in *.
  (* [comment removed for export] *)
  Ltac spec_cut G CUT rec nm :=
    pose proof (G rec) as nm; unfold CUT in nm;
    unfold S0F_bzd_snr1.CH, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in nm;
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in nm.
  (* [comment removed for export] *)
  Ltac l4_load i :=
    lazymatch goal with L4A : u8arr _ ?mm L4 _, R4 : forall i0 : Z, (0 <= zget (d_ll4 _) i0 < 256)%Z |- _ =>
      let RD := fresh "RD" in let R := fresh "Rv4" in
      pose proof (R4 i) as R;
      pose proof (zb8_read1 s0segs mm L4 (d_ll4 d0) (50000 * n) i _ L4A ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite zxb_lit8 by lia end.
  Ltac l16_load i :=
    lazymatch goal with L16A : u8arr _ ?mm L16 _, R16 : forall i0 : Z, (0 <= zget (d_ll16 _) i0 < 65536)%Z |- _ =>
      let RD := fresh "RD" in let R := fresh "Rv16" in
      pose proof (R16 i) as R;
      pose proof (zh16_read2 s0segs mm L16 (d_ll16 d0) (200000 * n) i _ L16A ltac:(lia) ltac:(lia) R eq_refl) as RD;
      wstep; clear RD; try rewrite (zx16_of_Z (zget (d_ll16 d0) i)) by lia end.
  Ltac name_sh tp sh :=
    let E := fresh "E" sh in let C := fresh "C" sh in
    remember (Z.land (tp * 4) 4) as sh eqn:E;
    pose proof (ll4_shift_cases tp) as C; rewrite <- E in C;
    let R := fresh "R" sh in assert (R : (0 <= sh <= 4)%Z) by lia; hide_disj.
  Ltac srlw_norm v4 sh :=
    rewrite (Z.mod_small sh 32) by lia; rewrite (swrap32_id (Z.shiftr v4 sh)) by lia;
    try rewrite (Z.mod_small (Z.shiftr v4 sh) 18446744073709551616) by lia.
  Ltac fold_ll v16 v4 tp sh Esh :=
    rewrite (shl60_shr44 (Z.shiftr v4 sh)) by (apply Z.shiftr_nonneg; lia);
    rewrite (lor_hi16 v16 (Z.shiftr v4 sh mod 16)) by (first [lia | apply Z.mod_pos_bound; lia]);
    replace (Z.shiftr v4 sh mod 16 * 65536 + v16)%Z with (llval v16 v4 tp) by (unfold llval; rewrite <- Esh; lia).
  Ltac nbu_fix v := match goal with H : rw_cells _ _ (_ + 1092)%Z [C4 (Z_to_bv 64 ?e)] |- _ => replace e with v in H by lia end.
  (* [comment removed for export] *)
  Ltac rn_load i :=
    lazymatch goal with RNA : u32arr _ ?mm 0x335b0 rnums_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read s0segs mm 0x335b0 rnums_words i (Z_to_bv 64 (rNums i)) _ RNA (rnums_words_nth i ltac:(lia)) ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite ?(sx32_of_Z (rNums i)) by lia end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_T2 : forall f', (forall p', R2S f' p') -> forall p, T2S f' p.
  Proof.
    intros f' IHR2 p. unfold S0F_bzd_sr1.T2S. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp Rv16p HSH.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst ol oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unAL.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    pose proof (get_sym_SR (set8 d0 k0 2 nu k0 tp rn rt cb) ltac:(s8; unfold blk_cap; lia) ltac:(s8; rewrite Esm, HSM; lia) ltac:(s8; rewrite RD1; lia)) as GS1.
    rewrite gsSR_set8 in GS1.
    rewrite (PG2_b _ _ _ _ _ _ GS1). clear GS1.
    pose proof (Rl16 tp) as R16. pose proof (Rl4 (tp / 2)%Z) as R4.
    rewrite (get_ll_llval d0 tp) by lia.
    pose proof (indexIntoF_range tp cf) as KR. set (k1 := indexIntoF tp cf) in *.
    pose proof (rNn_range rn rt ltac:(lia) ltac:(lia)) as RN1. pose proof (rTn_range rn rt ltac:(lia)) as RT1.
    (* [comment removed for export] *)
    UKit.urun_to 0x14bc4%Z.
    (* [comment removed for export] *)
    l4_load (tp / 2)%Z. set (v4 := zget (d_ll4 d0) (tp / 2)) in *.
    l16_load tp. set (v16' := zget (d_ll16 d0) tp) in *.
    (* [comment removed for export] *)
    wstep. wstep. rewrite HSH. name_sh tp sh. pose proof (shiftr_byte v4 sh ltac:(lia) ltac:(lia)) as SR4.
    (* [comment removed for export] *)
    wstep. srlw_norm v4 sh. wstep. wstep. wstep. fold_ll v16' v4 tp sh Esh.
    pose proof (llval_range v16' v4 tp ltac:(lia) ltac:(lia) ltac:(lia)) as TPR1. set (tp1 := llval v16' v4 tp) in *.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    wstep. if_cases K4; zify_cond K4.
    { rewrite (rNn_nz rn rt K4), (rTn_nz rn rt K4).
      spec_cut IHR2 S0F_bzd_sr1.R2S (PST k0 2 nu k0 tp1 rn rt cb out av tout tol toh) R2.
      enter_with (R2 _ _ _ _ _ k1 rn v16' _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close
        | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | subst tp1; symmetry; apply llval_bit2 ]. }
    wstep. try rewrite (sx32_of_Z rt) by lia. UKit.urun_to 0x14c1c%Z.
    rn_load rt. pose proof (rNums_range rt ltac:(lia)) as RNR.
    wstep. wstep. wstep. wstep. rewrite (rtpos_wrap rt) by lia.
    pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
    wstep. wstep.
    assert (Ez : rn = 0%Z) by lia. rewrite Ez. rewrite rNn_z, (rTn_z rt) by lia.
    spec_cut IHR2 S0F_bzd_sr1.R2S (PST k0 2 nu k0 tp1 (rNums rt) ((rt + 1) mod 512)%Z cb out av tout tol toh) R2.
    enter_with (R2 _ _ _ _ _ k1 (rNums rt) v16' _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close
        | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | subst tp1; symmetry; apply llval_bit2 ].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_R2 : forall f', (forall p', T3S f' p') -> (forall p', MS_ f' p') -> forall p, R2S f' p.
  Proof.
    intros f' IHT3 IHM p. unfold S0F_bzd_sr1.R2S. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp Hnb HrN1 Rv16p HSH.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst ol oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unAL.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    rewrite PG2b_eq. cbv zeta. s8.
    (* [comment removed for export] *)
    UKit.urun_to 0x14c58%Z. try nbu_fix (nu + 1)%Z.
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    { rewrite (proj2 (Z.eqb_eq (nu + 1) PP)) by lia.
      spec_cut IHM S0F_bzd_sr1.MS_ (PST k0 2 (nu + 1) k0 tp (rN1 - 1) rt cb out av tout tol toh) M.
      enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close | lia | lia ]. }
    rewrite (proj2 (Z.eqb_neq (nu + 1) PP)) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rewrite (mask_b2z rN1 HrN1). rewrite (land255_small nb) by lia.
    set (k1 := Z.lxor nb (rmask rN1)) in *.
    assert (Rk1 : (0 <= k1 < 256)%Z) by (subst k1; apply lxor_byte_bit; [lia | destruct (rN1 - 1 =? 1)%Z; lia]).
    (* [comment removed for export] *)
    wstep. if_cases K2; zify_cond K2.
    { rewrite (proj2 (Z.eqb_neq k1 k0)) by lia. cbn [negb].
      wstep. wstep.
      spec_cut IHM S0F_bzd_sr1.MS_ (PST k0 2 (nu + 1) k1 tp (rN1 - 1) rt cb out av tout tol toh) M.
      enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close | lia | lia ]. }
    rewrite (proj2 (Z.eqb_eq k1 k0)) by lia. cbn [negb]. s8.
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    wstep. if_cases K3; zify_cond K3.
    2:{ rewrite PG3_None by (apply get_sym_None; s8; unfold blk_cap; lia).
      wstep.
      eapply KE; [dsg_close | destg_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia]. }
    (* [comment removed for export] *)
    wstep. wstep.
    lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mm _) =>
      eapply (S0F_bzd_sr1.sr_B3 c OK OKS P mm tp) with (k := 7%nat) (t := 0%nat); [ro_close | lia | | reflexivity | reflexivity] end.
    intros s1' s8' t4' t6' lo hi E8.
    pose proof (iif_result cf tp lo hi E8) as RES.
    spec_cut IHT3 S0F_bzd_sr1.T3S (PST k0 3 (nu + 1) k0 tp (rN1 - 1) rt cb out av tout tol toh) T3.
    rewrite <- RES.
    enter_with (T3 _ _ _ _ _ v16 _ dbytes rest);
      [ st_eq
      | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
      | sinv_close
      | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | exact HSH ].
  Time Qed.
End SR.
End ACeilS1.
End S0F_bzd_sr4.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
Module S0F_bzd_sr5.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Arith.Wf_nat.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_outS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_fr1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_fr2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_outR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_snr1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_sr1.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

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
  Hypothesis OK : foctx_ok c. Hypothesis OKS : foctx_okS c. Hypothesis RD1 : d_rand (o_d c) = 1%Z.
  Hypothesis KJ : FKjoin c (FROs c).
  Hypothesis KE : FKexit c (FROs c).
  Hypothesis AL : foctx_al c.

  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation CH := (S0F_bzd_snr1.CH c). Notation sinvR := (S0F_bzd_sr1.sinvR c). Notation DR := (S0F_bzd_sr1.DR c).
  Notation MS_ := (S0F_bzd_sr1.MS_ c). Notation HS := (S0F_bzd_sr1.HS c). Notation OUTS := (S0F_bzd_sr1.OUTS c).
  Notation GS := (S0F_bzd_sr1.GS c).
  Notation T1S := (S0F_bzd_sr1.T1S c). Notation T2S := (S0F_bzd_sr1.T2S c). Notation T3S := (S0F_bzd_sr1.T3S c).
  Notation T4S := (S0F_bzd_sr1.T4S c). Notation T5S := (S0F_bzd_sr1.T5S c).
  Notation R1S := (S0F_bzd_sr1.R1S c). Notation R2S := (S0F_bzd_sr1.R2S c). Notation R3S := (S0F_bzd_sr1.R3S c).
  Notation R4S := (S0F_bzd_sr1.R4S c). Notation R5S := (S0F_bzd_sr1.R5S c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation cPP := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)) + 1)).
  Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)). Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).
  Notation nl16 := (Z_to_bv 64 (18446744073709551615 - b_ll16 (o_cx c))). Notation nl4 := (Z_to_bv 64 (18446744073709551615 - b_ll4 (o_cx c))).

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
  Ltac unAL := let AL' := fresh "AL" in pose proof AL as AL'; unfold foctx_al, ctx_al in AL'; cps_destruct AL' as ((ALs & ALsp & ALsrc & ALdst & ALtt & AL16 & AL4) & ALstrm).
  Ltac ro_close := unfold FROs, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.
  (* [comment removed for export] *)
  Ltac dsg_close := unfold DSg; focbn; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lazymatch goal with |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact_cells H end end].
  Ltac destg_close := unfold DESTg; focbn; repeat match goal with |- _ /\ _ => split end; first [eassumption | cbn [length]; lia].
  Ltac unhide_k0 := try match goal with H : id ((0 <= _ < 256)%Z \/ _) |- _ => unfold id in H end.
  Ltac sinv_close := unfold S0F_bzd_sr1.sinvR; cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh];
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  Ltac ojoin_close := unfold ojoin; focbn; unhide_k0; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lia | intros; lia | idtac].
  (* [comment removed for export] *)
  Ltac open_cut :=
    unfold S0F_bzd_snr1.CH, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_sr1.sinvR in *;
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in *.
  (* [comment removed for export] *)
  Ltac spec_cut G CUT rec nm :=
    pose proof (G rec) as nm; unfold CUT in nm;
    unfold S0F_bzd_snr1.CH, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in nm;
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in nm.
  (* [comment removed for export] *)
  Ltac l4_load i :=
    lazymatch goal with L4A : u8arr _ ?mm L4 _, R4 : forall i0 : Z, (0 <= zget (d_ll4 _) i0 < 256)%Z |- _ =>
      let RD := fresh "RD" in let R := fresh "Rv4" in
      pose proof (R4 i) as R;
      pose proof (zb8_read1 s0segs mm L4 (d_ll4 d0) (50000 * n) i _ L4A ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite zxb_lit8 by lia end.
  Ltac l16_load i :=
    lazymatch goal with L16A : u8arr _ ?mm L16 _, R16 : forall i0 : Z, (0 <= zget (d_ll16 _) i0 < 65536)%Z |- _ =>
      let RD := fresh "RD" in let R := fresh "Rv16" in
      pose proof (R16 i) as R;
      pose proof (zh16_read2 s0segs mm L16 (d_ll16 d0) (200000 * n) i _ L16A ltac:(lia) ltac:(lia) R eq_refl) as RD;
      wstep; clear RD; try rewrite (zx16_of_Z (zget (d_ll16 d0) i)) by lia end.
  Ltac name_sh tp sh :=
    let E := fresh "E" sh in let C := fresh "C" sh in
    remember (Z.land (tp * 4) 4) as sh eqn:E;
    pose proof (ll4_shift_cases tp) as C; rewrite <- E in C;
    let R := fresh "R" sh in assert (R : (0 <= sh <= 4)%Z) by lia; hide_disj.
  Ltac srlw_norm v4 sh :=
    rewrite (Z.mod_small sh 32) by lia; rewrite (swrap32_id (Z.shiftr v4 sh)) by lia;
    try rewrite (Z.mod_small (Z.shiftr v4 sh) 18446744073709551616) by lia.
  Ltac fold_ll v16 v4 tp sh Esh :=
    rewrite (shl60_shr44 (Z.shiftr v4 sh)) by (apply Z.shiftr_nonneg; lia);
    rewrite (lor_hi16 v16 (Z.shiftr v4 sh mod 16)) by (first [lia | apply Z.mod_pos_bound; lia]);
    replace (Z.shiftr v4 sh mod 16 * 65536 + v16)%Z with (llval v16 v4 tp) by (unfold llval; rewrite <- Esh; lia).
  Ltac nbu_fix v := match goal with H : rw_cells _ _ (_ + 1092)%Z [C4 (Z_to_bv 64 ?e)] |- _ => replace e with v in H by lia end.
  (* [comment removed for export] *)
  Ltac rn_load i :=
    lazymatch goal with RNA : u32arr _ ?mm 0x335b0 rnums_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read s0segs mm 0x335b0 rnums_words i (Z_to_bv 64 (rNums i)) _ RNA (rnums_words_nth i ltac:(lia)) ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite ?(sx32_of_Z (rNums i)) by lia end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_T3 : forall f', (forall p', R3S f' p') -> forall p, T3S f' p.
  Proof.
    intros f' IHR3 p. unfold S0F_bzd_sr1.T3S. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp Rv16p HSH.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst ol oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unAL.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    pose proof (get_sym_SR (set8 d0 k0 3 nu k0 tp rn rt cb) ltac:(s8; unfold blk_cap; lia) ltac:(s8; rewrite Esm, HSM; lia) ltac:(s8; rewrite RD1; lia)) as GS1.
    rewrite gsSR_set8 in GS1.
    rewrite (PG3_b _ _ _ _ _ _ GS1). clear GS1.
    pose proof (Rl16 tp) as R16. pose proof (Rl4 (tp / 2)%Z) as R4.
    rewrite (get_ll_llval d0 tp) by lia.
    pose proof (indexIntoF_range tp cf) as KR. set (k1 := indexIntoF tp cf) in *.
    pose proof (rNn_range rn rt ltac:(lia) ltac:(lia)) as RN1. pose proof (rTn_range rn rt ltac:(lia)) as RT1.
    (* [comment removed for export] *)
    UKit.urun_to 0x14d24%Z.
    (* [comment removed for export] *)
    l4_load (tp / 2)%Z. set (v4 := zget (d_ll4 d0) (tp / 2)) in *.
    l16_load tp. set (v16' := zget (d_ll16 d0) tp) in *.
    (* [comment removed for export] *)
    wstep. wstep. rewrite HSH. name_sh tp sh. pose proof (shiftr_byte v4 sh ltac:(lia) ltac:(lia)) as SR4.
    (* [comment removed for export] *)
    wstep. srlw_norm v4 sh. wstep. wstep. wstep. fold_ll v16' v4 tp sh Esh.
    pose proof (llval_range v16' v4 tp ltac:(lia) ltac:(lia) ltac:(lia)) as TPR1. set (tp1 := llval v16' v4 tp) in *.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    wstep. if_cases K4; zify_cond K4.
    { rewrite (rNn_nz rn rt K4), (rTn_nz rn rt K4).
      spec_cut IHR3 S0F_bzd_sr1.R3S (PST k0 3 nu k0 tp1 rn rt cb out av tout tol toh) R3.
      enter_with (R3 _ _ _ _ _ _ _ _ _ _ k1 rn _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close
        | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | lia ]. }
    wstep. try rewrite (sx32_of_Z rt) by lia. UKit.urun_to 0x14d7c%Z.
    rn_load rt. pose proof (rNums_range rt ltac:(lia)) as RNR.
    wstep. wstep. wstep. wstep. rewrite (rtpos_wrap rt) by lia.
    pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
    wstep. wstep.
    assert (Ez : rn = 0%Z) by lia. rewrite Ez. rewrite rNn_z, (rTn_z rt) by lia.
    spec_cut IHR3 S0F_bzd_sr1.R3S (PST k0 3 nu k0 tp1 (rNums rt) ((rt + 1) mod 512)%Z cb out av tout tol toh) R3.
    enter_with (R3 _ _ _ _ _ _ _ _ _ _ k1 (rNums rt) _ dbytes rest);
      [ st_eq
      | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
      | sinv_close
      | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | lia ].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_R3 : forall f', (forall p', T4S f' p') -> (forall p', MS_ f' p') -> forall p, R3S f' p.
  Proof.
    intros f' IHT4 IHM p. unfold S0F_bzd_sr1.R3S. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp Hnb HrN1.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst ol oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unAL.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    rewrite PG3b_eq. cbv zeta. s8.
    (* [comment removed for export] *)
    UKit.urun_to 0x14db0%Z. try nbu_fix (nu + 1)%Z.
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    { rewrite (proj2 (Z.eqb_eq (nu + 1) PP)) by lia.
      spec_cut IHM S0F_bzd_sr1.MS_ (PST k0 3 (nu + 1) k0 tp (rN1 - 1) rt cb out av tout tol toh) M.
      enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close | lia | lia ]. }
    rewrite (proj2 (Z.eqb_neq (nu + 1) PP)) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rewrite (mask_b2z rN1 HrN1). rewrite (land255_small nb) by lia.
    set (k1 := Z.lxor nb (rmask rN1)) in *.
    assert (Rk1 : (0 <= k1 < 256)%Z) by (subst k1; apply lxor_byte_bit; [lia | destruct (rN1 - 1 =? 1)%Z; lia]).
    (* [comment removed for export] *)
    wstep. if_cases K2; zify_cond K2.
    { rewrite (proj2 (Z.eqb_neq k1 k0)) by lia. cbn [negb].
      wstep. wstep.
      spec_cut IHM S0F_bzd_sr1.MS_ (PST k0 3 (nu + 1) k1 tp (rN1 - 1) rt cb out av tout tol toh) M.
      enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close | lia | lia ]. }
    rewrite (proj2 (Z.eqb_eq k1 k0)) by lia. cbn [negb]. s8.
    (* [comment removed for export] *)
    wstep. if_cases K3; zify_cond K3.
    { rewrite PG4_None by (apply get_sym_None; s8; unfold blk_cap; lia).
      eapply KE; [dsg_close | destg_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia]. }
    (* [comment removed for export] *)
    wstep. wstep.
    call (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.U0_idx.S0_indexIntoF.S0_indexIntoF_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S + 1096)%Z (zw32 cf 257)).
    1:{ exact CFA. } 1:{ exact (zw32_length_nat cf 257). } 1:{ assumption. } 1:{ lia. } 1:{ clear - ALs. Z.div_mod_to_equations. lia. } 1:{ reflexivity. }
    rewrite (signed_lit_small tp) by lia.
    rewrite (index_into_f_zw32 cf tp) by (intros i Hi; pose proof (Rcf ltac:(rewrite Esm, HSM; lia) i Hi); lia).
    spec_cut IHT4 S0F_bzd_sr1.T4S (PST k0 3 (nu + 1) k0 tp (rN1 - 1) rt cb out av tout tol toh) T4.
    enter_with (T4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ st_eq
      | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | assumption | assumption]
      | sinv_close
      | lia | lia | reflexivity | reflexivity | lia | lia | lia ].
  Time Qed.
End SR.
End ACeilS1.
End S0F_bzd_sr5.

Unset Lia Cache.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaS.
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
  Hypothesis OK : foctx_ok c. Hypothesis OKS : foctx_okS c. Hypothesis RD1 : d_rand (o_d c) = 1%Z.
  Hypothesis KJ : FKjoin c (FROs c).
  Hypothesis KE : FKexit c (FROs c).
  Hypothesis AL : foctx_al c.

  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation CH := (S0F_bzd_snr1.CH c). Notation sinvR := (S0F_bzd_sr1.sinvR c). Notation DR := (S0F_bzd_sr1.DR c).
  Notation MS_ := (S0F_bzd_sr1.MS_ c). Notation HS := (S0F_bzd_sr1.HS c). Notation OUTS := (S0F_bzd_sr1.OUTS c).
  Notation GS := (S0F_bzd_sr1.GS c).
  Notation T1S := (S0F_bzd_sr1.T1S c). Notation T2S := (S0F_bzd_sr1.T2S c). Notation T3S := (S0F_bzd_sr1.T3S c).
  Notation T4S := (S0F_bzd_sr1.T4S c). Notation T5S := (S0F_bzd_sr1.T5S c).
  Notation R1S := (S0F_bzd_sr1.R1S c). Notation R2S := (S0F_bzd_sr1.R2S c). Notation R3S := (S0F_bzd_sr1.R3S c).
  Notation R4S := (S0F_bzd_sr1.R4S c). Notation R5S := (S0F_bzd_sr1.R5S c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation cPP := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)) + 1)).
  Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)). Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).
  Notation nl16 := (Z_to_bv 64 (18446744073709551615 - b_ll16 (o_cx c))). Notation nl4 := (Z_to_bv 64 (18446744073709551615 - b_ll4 (o_cx c))).

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
  Ltac unAL := let AL' := fresh "AL" in pose proof AL as AL'; unfold foctx_al, ctx_al in AL'; cps_destruct AL' as ((ALs & ALsp & ALsrc & ALdst & ALtt & AL16 & AL4) & ALstrm).
  Ltac ro_close := unfold FROs, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.
  (* [comment removed for export] *)
  Ltac dsg_close := unfold DSg; focbn; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lazymatch goal with |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact_cells H end end].
  Ltac destg_close := unfold DESTg; focbn; repeat match goal with |- _ /\ _ => split end; first [eassumption | cbn [length]; lia].
  Ltac unhide_k0 := try match goal with H : id ((0 <= _ < 256)%Z \/ _) |- _ => unfold id in H end.
  Ltac sinv_close := unfold S0F_bzd_sr1.sinvR; cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh];
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  Ltac ojoin_close := unfold ojoin; focbn; unhide_k0; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lia | intros; lia | idtac].
  (* [comment removed for export] *)
  Ltac open_cut :=
    unfold S0F_bzd_snr1.CH, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_sr1.sinvR in *;
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in *.
  (* [comment removed for export] *)
  Ltac spec_cut G CUT rec nm :=
    pose proof (G rec) as nm; unfold CUT in nm;
    unfold S0F_bzd_snr1.CH, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in nm;
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in nm.
  (* [comment removed for export] *)
  Ltac l4_load i :=
    lazymatch goal with L4A : u8arr _ ?mm L4 _, R4 : forall i0 : Z, (0 <= zget (d_ll4 _) i0 < 256)%Z |- _ =>
      let RD := fresh "RD" in let R := fresh "Rv4" in
      pose proof (R4 i) as R;
      pose proof (zb8_read1 s0segs mm L4 (d_ll4 d0) (50000 * n) i _ L4A ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite zxb_lit8 by lia end.
  Ltac l16_load i :=
    lazymatch goal with L16A : u8arr _ ?mm L16 _, R16 : forall i0 : Z, (0 <= zget (d_ll16 _) i0 < 65536)%Z |- _ =>
      let RD := fresh "RD" in let R := fresh "Rv16" in
      pose proof (R16 i) as R;
      pose proof (zh16_read2 s0segs mm L16 (d_ll16 d0) (200000 * n) i _ L16A ltac:(lia) ltac:(lia) R eq_refl) as RD;
      wstep; clear RD; try rewrite (zx16_of_Z (zget (d_ll16 d0) i)) by lia end.
  Ltac name_sh tp sh :=
    let E := fresh "E" sh in let C := fresh "C" sh in
    remember (Z.land (tp * 4) 4) as sh eqn:E;
    pose proof (ll4_shift_cases tp) as C; rewrite <- E in C;
    let R := fresh "R" sh in assert (R : (0 <= sh <= 4)%Z) by lia; hide_disj.
  Ltac srlw_norm v4 sh :=
    rewrite (Z.mod_small sh 32) by lia; rewrite (swrap32_id (Z.shiftr v4 sh)) by lia;
    try rewrite (Z.mod_small (Z.shiftr v4 sh) 18446744073709551616) by lia.
  Ltac fold_ll v16 v4 tp sh Esh :=
    rewrite (shl60_shr44 (Z.shiftr v4 sh)) by (apply Z.shiftr_nonneg; lia);
    rewrite (lor_hi16 v16 (Z.shiftr v4 sh mod 16)) by (first [lia | apply Z.mod_pos_bound; lia]);
    replace (Z.shiftr v4 sh mod 16 * 65536 + v16)%Z with (llval v16 v4 tp) by (unfold llval; rewrite <- Esh; lia).
  Ltac nbu_fix v := match goal with H : rw_cells _ _ (_ + 1092)%Z [C4 (Z_to_bv 64 ?e)] |- _ => replace e with v in H by lia end.
  (* [comment removed for export] *)
  Ltac rn_load i :=
    lazymatch goal with RNA : u32arr _ ?mm 0x335b0 rnums_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read s0segs mm 0x335b0 rnums_words i (Z_to_bv 64 (rNums i)) _ RNA (rnums_words_nth i ltac:(lia)) ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite ?(sx32_of_Z (rNums i)) by lia end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_T4 : forall f', (forall p', R4S f' p') -> forall p, T4S f' p.
  Proof.
    intros f' IHR4 p. unfold S0F_bzd_sr1.T4S. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst ol oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unAL.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    pose proof (get_sym_SR (set8 d0 k0 3 nu k0 tp rn rt cb) ltac:(s8; unfold blk_cap; lia) ltac:(s8; rewrite Esm, HSM; lia) ltac:(s8; rewrite RD1; lia)) as GS1.
    rewrite gsSR_set8 in GS1.
    rewrite (PG4_b _ _ _ _ _ GS1). clear GS1.
    pose proof (Rl16 tp) as R16. pose proof (Rl4 (tp / 2)%Z) as R4.
    rewrite (get_ll_llval d0 tp) by lia.
    pose proof (indexIntoF_range tp cf) as KR. set (k1 := indexIntoF tp cf) in *.
    pose proof (rNn_range rn rt ltac:(lia) ltac:(lia)) as RN1. pose proof (rTn_range rn rt ltac:(lia)) as RT1.
    (* [comment removed for export] *)
    UKit.urun_to 0x14e28%Z.
    (* [comment removed for export] *)
    l4_load (tp / 2)%Z. set (v4 := zget (d_ll4 d0) (tp / 2)) in *.
    (* [comment removed for export] *)
    l16_load tp. set (v16' := zget (d_ll16 d0) tp) in *.
    (* [comment removed for export] *)
    wstep. wstep. name_sh tp sh. pose proof (shiftr_byte v4 sh ltac:(lia) ltac:(lia)) as SR4.
    (* [comment removed for export] *)
    wstep. srlw_norm v4 sh. wstep. try rewrite (sx32_of_Z rn) by lia. wstep. wstep. wstep. fold_ll v16' v4 tp sh Esh.
    pose proof (llval_range v16' v4 tp ltac:(lia) ltac:(lia) ltac:(lia)) as TPR1. set (tp1 := llval v16' v4 tp) in *.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    wstep. if_cases K4; zify_cond K4.
    { rewrite (rNn_nz rn rt K4), (rTn_nz rn rt K4).
      spec_cut IHR4 S0F_bzd_sr1.R4S (PST k0 3 nu k0 tp1 rn rt cb out av tout tol toh) CR4.
      enter_with (CR4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k1 rn _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close
        | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | lia ]. }
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z rt) by lia. UKit.urun_to 0x14e7c%Z.
    rn_load rt. pose proof (rNums_range rt ltac:(lia)) as RNR.
    wstep. wstep. wstep. wstep. rewrite (rtpos_wrap rt) by lia.
    pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
    wstep. wstep.
    assert (Ez : rn = 0%Z) by lia. rewrite Ez. rewrite rNn_z, (rTn_z rt) by lia.
    spec_cut IHR4 S0F_bzd_sr1.R4S (PST k0 3 nu k0 tp1 (rNums rt) ((rt + 1) mod 512)%Z cb out av tout tol toh) CR4.
    enter_with (CR4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k1 (rNums rt) _ dbytes rest);
      [ st_eq
      | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
      | sinv_close
      | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | lia ].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_R4 : forall f', (forall p', T5S f' p') -> forall p, R4S f' p.
  Proof.
    intros f' IHT5 p. unfold S0F_bzd_sr1.R4S. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp Hnb HrN1.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst ol oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unAL.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    unfold PG4b. s8.
    (* [comment removed for export] *)
    UKit.urun_to 0x14ec4%Z. try nbu_fix (nu + 1)%Z. rewrite (land255_small nb) by lia.
    wstep. rewrite (mask_b2z rN1 HrN1).
    set (k1 := Z.lxor nb (rmask rN1)) in *.
    assert (Rk1 : (0 <= k1 < 256)%Z) by (subst k1; apply lxor_byte_bit; [lia | destruct (rN1 - 1 =? 1)%Z; lia]).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep. if_cases K3; zify_cond K3.
    { rewrite PG5_None by (apply get_sym_None; s8; unfold blk_cap; lia).
      eapply KE; [dsg_close | destg_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia]. }
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    call (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.U0_idx.S0_indexIntoF.S0_indexIntoF_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S + 1096)%Z (zw32 cf 257)).
    1:{ exact CFA. } 1:{ exact (zw32_length_nat cf 257). } 1:{ assumption. } 1:{ lia. } 1:{ clear - ALs. Z.div_mod_to_equations. lia. } 1:{ reflexivity. }
    rewrite (signed_lit_small tp) by lia.
    rewrite (index_into_f_zw32 cf tp) by (intros i Hi; pose proof (Rcf ltac:(rewrite Esm, HSM; lia) i Hi); lia).
    spec_cut IHT5 S0F_bzd_sr1.T5S (PST k0 (k1 + 4) (nu + 1) k0 tp (rN1 - 1) rt cb out av tout tol toh) T5.
    enter_with (T5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ st_eq
      | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | assumption | assumption]
      | sinv_close
      | lia | lia | lia | reflexivity | lia | lia | lia ].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_T5 : forall f', (forall p', R5S f' p') -> forall p, T5S f' p.
  Proof.
    intros f' IHR5 p. unfold S0F_bzd_sr1.T5S. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unAL.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    pose proof (get_sym_SR (set8 d0 k0 ol nu k0 tp rn rt cb) ltac:(s8; unfold blk_cap; lia) ltac:(s8; rewrite Esm, HSM; lia) ltac:(s8; rewrite RD1; lia)) as GS1.
    rewrite gsSR_set8 in GS1.
    rewrite (PG5_Some _ _ _ _ _ GS1). clear GS1. s8.
    pose proof (Rl16 tp) as R16. pose proof (Rl4 (tp / 2)%Z) as R4.
    rewrite (get_ll_llval d0 tp) by lia.
    pose proof (indexIntoF_range tp cf) as KR. set (k1 := indexIntoF tp cf) in *.
    pose proof (rNn_range rn rt ltac:(lia) ltac:(lia)) as RN1. pose proof (rTn_range rn rt ltac:(lia)) as RT1.
    (* [comment removed for export] *)
    UKit.urun_to 0x14f3c%Z.
    (* [comment removed for export] *)
    l4_load (tp / 2)%Z. set (v4 := zget (d_ll4 d0) (tp / 2)) in *.
    (* [comment removed for export] *)
    l16_load tp. set (v16' := zget (d_ll16 d0) tp) in *.
    (* [comment removed for export] *)
    wstep. wstep. name_sh tp sh. pose proof (shiftr_byte v4 sh ltac:(lia) ltac:(lia)) as SR4.
    (* [comment removed for export] *)
    wstep. srlw_norm v4 sh. wstep. try rewrite (sx32_of_Z rn) by lia. wstep. wstep. wstep. fold_ll v16' v4 tp sh Esh.
    pose proof (llval_range v16' v4 tp ltac:(lia) ltac:(lia) ltac:(lia)) as TPR1. set (tp1 := llval v16' v4 tp) in *.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    wstep. if_cases K4; zify_cond K4.
    { rewrite (rNn_nz rn rt K4), (rTn_nz rn rt K4).
      spec_cut IHR5 S0F_bzd_sr1.R5S (PST k0 ol nu k1 tp1 rn rt cb out av tout tol toh) R5.
      enter_with (R5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rn _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close
        | lia | lia | lia | lia | lia | lia | lia ]. }
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z rt) by lia. UKit.urun_to 0x14f90%Z.
    rn_load rt. pose proof (rNums_range rt ltac:(lia)) as RNR.
    wstep. wstep. wstep. wstep. rewrite (rtpos_wrap rt) by lia.
    pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
    wstep. wstep.
    assert (Ez : rn = 0%Z) by lia. rewrite Ez. rewrite rNn_z, (rTn_z rt) by lia.
    spec_cut IHR5 S0F_bzd_sr1.R5S (PST k0 ol nu k1 tp1 (rNums rt) ((rt + 1) mod 512)%Z cb out av tout tol toh) R5.
    enter_with (R5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rNums rt) _ dbytes rest);
      [ st_eq
      | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
      | sinv_close
      | lia | lia | lia | lia | lia | lia | lia ].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_R5 : forall f', (forall p', MS_ f' p') -> forall p, R5S f' p.
  Proof.
    intros f' IHM p. unfold S0F_bzd_sr1.R5S. intros until rest. intros CHm SI Hf Hav Hol Rk0 Hnu Htp HrN1.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unAL.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    UKit.urun_to 0x14fc4%Z. rewrite (mask_b2z rN1 HrN1).
    set (k5 := Z.lxor k0 (rmask rN1)) in *.
    assert (Rk5 : (0 <= k5 < 256)%Z) by (subst k5; apply lxor_byte_bit; [lia | destruct (rN1 - 1 =? 1)%Z; lia]).
    (* [comment removed for export] *)
    UKit.urun_to 0x14fe4%Z. try nbu_fix (nu + 1)%Z.
    spec_cut IHM S0F_bzd_sr1.MS_ (PST oc ol (nu + 1) k5 tp (rN1 - 1) rt cb out av tout tol toh) M.
    enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close | lia | lia ].
  Time Qed.
End SR.
End ACeilS1.
