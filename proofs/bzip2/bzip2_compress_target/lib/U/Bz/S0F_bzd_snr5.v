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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_out S0F_bzd_outS S0F_bzd_snr1.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_out S0F_bzd_outS S0F_bzd_snr1 UKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
Module S0F_bzd_snr2.
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
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_outS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_snr1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.UKit.
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

Section SNR.
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
    (FRR c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) (only parsing).
  Hypothesis OK : foctx_ok c. Hypothesis OKS : foctx_okS c. Hypothesis AL : foctx_al c. Hypothesis RD0 : d_rand (o_d c) = 0%Z.
  Hypothesis KJ : FKjoin c (FROs c).
  Hypothesis KE : FKexit c (FROs c).

  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation sinv := (S0F_bzd_snr1.sinv c). Notation CH := (S0F_bzd_snr1.CH c).
  Notation MS_ := (S0F_bzd_snr1.MS_ c). Notation HS := (S0F_bzd_snr1.HS c). Notation OUTS := (S0F_bzd_snr1.OUTS c).
  Notation GS := (S0F_bzd_snr1.GS c).
  Notation T1S := (S0F_bzd_snr1.T1S c). Notation T2S := (S0F_bzd_snr1.T2S c). Notation T3S := (S0F_bzd_snr1.T3S c).
  Notation T4S := (S0F_bzd_snr1.T4S c). Notation T5S := (S0F_bzd_snr1.T5S c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation csnb := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)))).
  Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)).
  Notation c14 := (Z_to_bv 64 14). Notation c3 := (Z_to_bv 64 3). Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).

  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & L16A & L4A & CFA & CRC & RNA & GOT & MI); unfold FGOT in GOT.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac unCH H := let DSm := fresh "DSm" in let DE := fresh "DE" in let ROm := fresh "ROm" in
    cps_destruct H as (DSm & DE & ROm & MU & WM); unDS DSm; cps_destruct DE as (DSTA & DL & Edb & Lout); unRO ROm.
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & SEP_SD & IAS & IAD & JWF & ENT);
    let OKS' := fresh "OKS" in pose proof OKS as OKS';
    cps_destruct OKS' as (HSM & HL16 & HL4 & SEP_S16 & SEP_D16 & SEP_S4 & SEP_D4 & SEP_164);
    let AL' := fresh "AL" in pose proof AL as AL'; unfold foctx_al, ctx_al in AL';
    cps_destruct AL' as ((ALs & ALsp & ALsrc & ALdst & ALtt & AL16 & AL4) & ALstrm);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & Rcf & Rtt & Rl16 & Rl4);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold FWB in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length cf 257 ltac:(lia)) as CFL;
    pose proof (zh16_length (d_ll16 d0) (200000 * n) ltac:(lia)) as L16L; pose proof (zb8_length (d_ll4 d0) (50000 * n) ltac:(lia)) as L4L;
    pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL; hide_disj.
  Ltac ro_close := unfold FROs, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.
  (* [comment removed for export] *)
  Ltac dsg_close := unfold DSg; focbn; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lazymatch goal with |- rw_cells _ _ _ _ => idtac end; match goal with H : rw_cells _ _ _ _ |- _ => exact_cells H end].
  Ltac destg_close := unfold DESTg; focbn; repeat match goal with |- _ /\ _ => split end; first [eassumption | cbn [length]; lia].
  (* [comment removed for export] *)
  Ltac unhide_k0 := try match goal with H : id ((0 <= _ < 256)%Z \/ _) |- _ => unfold id in H end.
  Ltac sinv_close := unfold S0F_bzd_snr1.sinv; cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh];
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma snr_G : forall f, (forall f' p', f = Datatypes.S f' -> T1S f' p') -> forall p, GS f p.
  Proof using OK OKS AL RD0 KJ KE.
    intros f IHT1 p. unfold S0F_bzd_snr1.GS. intros until rest. intros CHm SI Hf Hav Hol.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold S0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in *.
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in *. subst ol.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z snb) by lia. urun_to 0x15520%Z. wstep. try rewrite (sx32_of_Z nu) by lia.
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      rewrite K_PG_done by (s8; lia).
      eapply KJ; [dsg_close | destg_close | ro_close | exact MU | exact WM | ].
      unfold ojoin. focbn. unhide_k0. repeat match goal with |- _ /\ _ => split end; first [assumption | lia | intros; exfalso; rewrite RD0 in *; lia | idtac]. }
    (* [comment removed for export] *)
    wstep. wstep. if_cases K2; zify_cond K2; rewrite ?signed_lit_small in K2 by lia.
    { rewrite K_PG_over by (s8; lia).
      eapply KE; [dsg_close | destg_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia]. }
    rewrite K_PG_go by (s8; lia). s8.
    (* [comment removed for export] *)
    wstep. try rewrite (zx32_of_Z tp) by lia. wstep. rewrite ?En. try rewrite (sx32_of_Z n) by lia. wstep.
    unfold id in Rk0. destruct Rk0 as [Rk0 | [Hnu0 Htp0]].
    - (* [comment removed for export] *)
      try rewrite (sx32_of_Z k0) by lia.
      wstep. wstep.
      (* [comment removed for export] *)
      step. rewrite BzInv.le1_lit. mem_after_store. try rewrite (unsigned_lit k0) in HD by lia. wstep.
      (* [comment removed for export] *)
      pose proof (word_urange (Z_to_bv 64 tp)) as TPR.
      wstep. if_cases K3; zify_cond K3.
      { (* [comment removed for export] *)
        assert (K3' : (cap <= bv_swrap 32 (tp + 0) mod 18446744073709551616)%Z) by lia.
        pose proof (sextw_ge tp cap ltac:(lia) ltac:(lia) K3') as GE.
        change (2^32)%Z with 4294967296%Z in GE. rewrite (Z.mod_small tp 4294967296) in GE by lia.
        rewrite PG1_None by (apply get_sym_None; s8; unfold blk_cap; lia).
        eapply KE; [dsg_close | destg_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia]. }
      assert (K3' : (bv_swrap 32 (tp + 0) mod 18446744073709551616 < cap)%Z) by lia.
      destruct (sextw_lt tp cap ltac:(lia) ltac:(lia) K3') as [LT XV].
      change (2^32)%Z with 4294967296%Z in LT, XV. rewrite (Z.mod_small tp 4294967296) in LT, XV by lia.
      replace (Z_to_bv 64 (bv_swrap 32 (tp + 0))) with (Z_to_bv 64 tp) by (f_equal; rewrite swrap32_id by lia; lia).
      (* [comment removed for export] *)
      wstep. wstep.
      destruct f as [|f']; [exfalso; cbn [Z.of_nat] in Hf; lia|]. rewrite Nat2Z.inj_succ in Hf.
      lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mm _) =>
        eapply (S0F_bzd_snr1.snr_B1 c OK OKS P mm tp) with (k := 7%nat) (t := 0%nat);
        [ro_close | lia | | reflexivity | reflexivity] end.
      intros t0' t1' t2' t3' lo hi E8.
      pose proof (iif_result cf tp lo hi E8) as RES.
      pose proof (IHT1 f' (PST k0 1 nu k0 tp rn rt cb out av tout tol toh) eq_refl) as T1. unfold S0F_bzd_snr1.T1S in T1.
      cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in T1. unfold S0F_bzd_snr1.CH in T1; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in T1.
      rewrite <- RES.
      enter_with (T1 _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close
        | lia | lia | reflexivity | reflexivity | lia | lia | lia ].
    - (* [comment removed for export] *)
      subst nu.
      wstep. wstep.
      step. rewrite ?le1_sx32_lit, ?BzInv.le1_lit. mem_after_store. wstep.
      pose proof (word_urange (Z_to_bv 64 tp)) as TPR.
      wstep. if_cases K3; zify_cond K3.
      2:{ exfalso. assert (K3' : (bv_swrap 32 (tp + 0) mod 18446744073709551616 < cap)%Z) by lia.
          destruct (sextw_lt tp cap ltac:(lia) ltac:(lia) K3') as [LT _].
          change (2^32)%Z with 4294967296%Z in LT. rewrite (Z.mod_small tp 4294967296) in LT by lia. lia. }
      rewrite PG1_None by (apply get_sym_None; s8; unfold blk_cap; lia).
      eapply KE; [dsg_close | destg_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia].
  Time Qed.
End SNR.
End ACeilS1.
End S0F_bzd_snr2.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_snr3 S0F_bzd_snr4 S0F_bzd_vspec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_outS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_snr1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_snr5.S0F_bzd_snr2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_snr3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_snr4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_vspec.
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
Section SNR.
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
    (FRR c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) (only parsing).
  Hypothesis OK : foctx_ok c. Hypothesis OKS : foctx_okS c. Hypothesis AL : foctx_al c. Hypothesis RD0 : d_rand (o_d c) = 0%Z.
  Hypothesis KJ : FKjoin c (FROs c).
  Hypothesis KE : FKexit c (FROs c).

  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation sinv := (S0F_bzd_snr1.sinv c). Notation CH := (S0F_bzd_snr1.CH c).
  Notation MS_ := (S0F_bzd_snr1.MS_ c). Notation HS := (S0F_bzd_snr1.HS c). Notation OUTS := (S0F_bzd_snr1.OUTS c).
  Notation GS := (S0F_bzd_snr1.GS c).
  Notation T1S := (S0F_bzd_snr1.T1S c). Notation T2S := (S0F_bzd_snr1.T2S c). Notation T3S := (S0F_bzd_snr1.T3S c).
  Notation T4S := (S0F_bzd_snr1.T4S c). Notation T5S := (S0F_bzd_snr1.T5S c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation csnb := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)))).
  Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)).
  Notation c14 := (Z_to_bv 64 14). Notation c3 := (Z_to_bv 64 3). Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).

  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & L16A & L4A & CFA & CRC & RNA & GOT & MI); unfold FGOT in GOT.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac unCH H := let DSm := fresh "DSm" in let DE := fresh "DE" in let ROm := fresh "ROm" in
    cps_destruct H as (DSm & DE & ROm & MU & WM); unDS DSm; cps_destruct DE as (DSTA & DL & Edb & Lout); unRO ROm.
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & SEP_SD & IAS & IAD & JWF & ENT);
    let OKS' := fresh "OKS" in pose proof OKS as OKS';
    cps_destruct OKS' as (HSM & HL16 & HL4 & SEP_S16 & SEP_D16 & SEP_S4 & SEP_D4 & SEP_164);
    let AL' := fresh "AL" in pose proof AL as AL'; unfold foctx_al, ctx_al in AL';
    cps_destruct AL' as ((ALs & ALsp & ALsrc & ALdst & ALtt & AL16 & AL4) & ALstrm);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & Rcf & Rtt & Rl16 & Rl4);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold FWB in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length cf 257 ltac:(lia)) as CFL;
    pose proof (zh16_length (d_ll16 d0) (200000 * n) ltac:(lia)) as L16L; pose proof (zb8_length (d_ll4 d0) (50000 * n) ltac:(lia)) as L4L;
    pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL; hide_disj.
  Ltac ro_close := unfold FROs, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.
  (* [comment removed for export] *)
  Ltac dsg_close := unfold DSg; focbn; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lazymatch goal with |- rw_cells _ _ _ _ => idtac end; match goal with H : rw_cells _ _ _ _ |- _ => exact_cells H end].
  Ltac destg_close := unfold DESTg; focbn; repeat match goal with |- _ /\ _ => split end; first [eassumption | cbn [length]; lia].
  (* [comment removed for export] *)
  Ltac unhide_k0 := try match goal with H : id ((0 <= _ < 256)%Z \/ _) |- _ => unfold id in H end.
  Ltac sinv_close := unfold S0F_bzd_snr1.sinv; cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh];
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac dst_write av oc :=
    lazymatch goal with DSTA : u8arr _ _ DST ?bs, Edb : _ = map _ (rev ?out) ++ ?rst |- _ =>
      lazymatch goal with DL : Z.of_nat (length bs) = _ |- _ =>
      (* [comment removed for export] *)
      let r0 := fresh "r0" in let rest' := fresh "rest" in let LR := fresh "LR" in
      pose proof (f_equal (@length byte) Edb) as LR; rewrite length_app, length_map, length_rev in LR;
      destruct rst as [|r0 rest']; [exfalso; cbn [length] in LR; lia|]; cbn [length] in LR;
      let E' := fresh "Edb" in
      pose proof (dest_snoc out (r0 :: rest') oc r0 rest' eq_refl) as E';
      replace (length out) with (Z.to_nat (dlen - av)) in E' by lia; rewrite <- Edb in E'; clear Edb LR;
      (* [comment removed for export] *)
      let SOK := fresh "SOK" in
      pose proof (u8arr_store_ok s0segs _ DST _ (dlen - av) _ DSTA ltac:(lia) eq_refl) as SOK;
      step; rewrite BzInv.le1_lit;
      let D := fresh "DSTB" in
      pose proof (u8arr_write s0segs _ DST _ (dlen - av) (Z_to_bv 8 oc) DSTA ltac:(lia)) as D;
      clear DSTA; store_done; try clear SOK; rename D into DSTA;
      let D2 := fresh "DLB" in
      pose proof DL as D2; rewrite <- (upd_length bs (Z.to_nat (dlen - av)) (Z_to_bv 8 oc)) in D2; clear DL; rename D2 into DL;
      let db := fresh "dbytes" in
      remember (upd bs (Z.to_nat (dlen - av)) (Z_to_bv 8 oc)) as db eqn:Xdb; clear Xdb; rename E' into Edb
      end end.
  (* [comment removed for export] *)
  Ltac crc_load crc ch :=
    let Hidx := fresh "Hidx" in
    pose proof (crc_idx_byte crc ch ltac:(lia) ltac:(lia)) as Hidx;
    lazymatch goal with CRC : u32arr _ ?mm 209272 crc_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read s0segs mm 209272 crc_words (Z.lxor (crc / 16777216) ch) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD;
      wstep; clear RD end; clear Hidx.
  (* [comment removed for export] *)
  Ltac cs_split cs w :=
    lazymatch cs with
    | C4 w :: ?post => constr:((@nil cell, post))
    | ?c1 :: ?cs' => let r := cs_split cs' w in lazymatch r with (?pre, ?post) => constr:((c1 :: pre, post)) end
    end.
  Ltac recell H w v :=
    lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
      let r := cs_split cs w in
      lazymatch r with (?pre, ?post) =>
        apply (C4_recell sg mm A pre w v post) in H; [ cbn [app] in H | ]
      end
    end.

  Lemma crc_step_relU : forall crc ch, (0 <= crc < 4294967296)%Z -> (0 <= ch < 256)%Z ->
    (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (sx32 (Z_to_bv 64 (crc32_tbl (Z.lxor (crc / 16777216) ch))))) (crc * 256)))
       mod 4294967296 = crc_update crc ch)%Z.
  Proof.
    intros crc ch Hc Hch.
    pose proof (crc_step_rel (Z_to_bv 64 crc) crc ch ltac:(rewrite unsigned_lit by Lia.lia; apply Z.mod_small; Lia.lia) Hc Hch) as E.
    rewrite (unsigned_lit crc) in E by Lia.lia. rewrite (Z.mod_small (crc * 256) 18446744073709551616) in E by Lia.lia. exact E.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma snr_OUT : forall f p,
    (forall p', p_ol p' = (p_ol p - 1)%Z -> HS f p') -> OUTS f p.
  Proof.
    intros f p IHH. unfold S0F_bzd_snr1.OUTS. intros until rest. intros CHm SI Hf Hav Hol.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold S0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in *.
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in *.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    rewrite K_PH_step by (s8; lia). cbv zeta. s8.
    (* [comment removed for export] *)
    wstep. wstep. notrap. wstep. rewrite ?zxb_lit8 by lia.
    (* [comment removed for export] *)
    dst_write av oc.
    (* [comment removed for export] *)
    wstep. wstep. rewrite ?zxb_lit8 by lia. wstep. wstep. wstep. wstep. wstep. wstep.
    pose proof (crc_idx_byte cb oc ltac:(lia) ltac:(lia)) as CIR. wstep. notrap. wstep.
    (* [comment removed for export] *)
    crc_load cb oc. clear CIR.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z ol) by lia. wstep. wstep. wstep.
    pose proof (crc_update_range cb oc ltac:(lia)) as CR'.
    (* [comment removed for export] *)
    wstep.
    lazymatch type of MID with context [C4 (Z_to_bv 64 (Z.lxor ?a ?b))] => recell MID (Z_to_bv 64 (Z.lxor a b)) (crc_update cb oc) end.
    2:{ rewrite (Z.mod_small (crc_update cb oc) 4294967296) by exact CR'. apply crc_step_relU; lia. }
    (* [comment removed for export] *)
    wstep. notrap. wstep. wstep. wstep. notrap. wstep. wstep. notrap.
    wstep. wstep. wstep. notrap.
    wstep. try rewrite (sx32_of_Z av) by lia. wstep. wstep. wstep. wstep. wstep. wstep.
    replace (DST + (dlen - av) + 1)%Z with (DST + (dlen - (av - 1)))%Z in SM by lia.
    unfold S0F_bzd_snr1.HS in IHH.
    (* [comment removed for export] *)
    Ltac fin IHH MU WM oc ol nu k0 tp rn rt cb out av tout :=
      let KA := fresh "KA" in
      wstep; if_cases KA; zify_cond KA;
      [ (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_eq (av - 1) 0)) by lia;
        eapply KJ; [dsg_close | destg_close | ro_close | exact MU | exact WM | ];
        unfold ojoin; focbn; unhide_k0; repeat match goal with |- _ /\ _ => split end; first [assumption | lia | intros; exfalso; rewrite RD0 in *; lia | idtac]
      | rewrite (proj2 (Z.eqb_neq (av - 1) 0)) by lia;
        enter_with (IHH (PST oc (ol - 1) nu k0 tp rn rt (crc_update cb oc) (oc :: out) (av - 1) (tout + 1) _ _) eq_refl);
        [ cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh]; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss; st_eq
        | unfold S0F_bzd_snr1.CH; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp;
          cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh];
          repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close
        | cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh]; lia
        | cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh]; lia ] ].
    wstep. if_cases KT; zify_cond KT.
    - fin IHH MU WM oc ol nu k0 tp rn rt cb out av tout.
    - wstep. wstep. wstep. wstep. fin IHH MU WM oc ol nu k0 tp rn rt cb out av tout.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma snr_H : forall f p, GS f p -> OUTS f p -> HS f p.
  Proof.
    intros f p G O. unfold S0F_bzd_snr1.HS. intros until rest. intros CHm SI Hf Hav.
    pose proof CHm as CH0. pose proof SI as SI0.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold S0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in CHm, SI, Hf, Hav |- *.
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in *.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z ol) by lia. wstep. if_cases K0; zify_cond K0.
    - rewrite K_PH_0 by (s8; lia). unfold S0F_bzd_snr1.GS in G. eapply G; [exact CH0 | exact SI0 | cbn [p_nu]; lia | cbn [p_av]; lia | cbn [p_ol]; lia].
    - unfold S0F_bzd_snr1.OUTS in O. eapply O; [exact CH0 | exact SI0 | cbn [p_nu]; lia | cbn [p_av]; lia | cbn [p_ol]; lia].
  Time Qed.

  Lemma snr_M : forall f p, OUTS f p -> MS_ f p.
  Proof.
    intros f p O. unfold S0F_bzd_snr1.MS_. intros until rest. intros CHm SI Hf Hol.
    pose proof CHm as CH0. pose proof SI as SI0.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold S0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in CHm, SI, Hf, Hol |- *.
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in *.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    wstep. wstep. notrap. wstep. wstep. notrap.
    wstep. try rewrite (sx32_of_Z av) by lia.
    wstep. if_cases K0; zify_cond K0.
    - rewrite K_PM_ret by (s8; lia).
      eapply KJ; [dsg_close | destg_close | ro_close | exact MU | exact WM | ].
      unfold ojoin. focbn. unhide_k0. repeat match goal with |- _ /\ _ => split end; first [assumption | lia | intros; exfalso; rewrite RD0 in *; lia | idtac].
    - rewrite K_PM_go by (s8; lia).
      wstep. try rewrite (sx32_of_Z ol) by lia. wstep. if_cases K1; zify_cond K1; [exfalso; lia |].
      unfold S0F_bzd_snr1.OUTS in O. eapply O; [exact CH0 | exact SI0 | cbn [p_nu]; lia | cbn [p_av]; lia | cbn [p_ol]; lia].
  Time Qed.

  (* [comment removed for export] *)
  Lemma snr_HO : forall f, (forall p, GS f p) -> forall k p, Z.to_nat (p_ol p) = k -> HS f p /\ OUTS f p.
  Proof.
    intros f G k. induction k as [k IH] using lt_wf_ind. intros p Hk.
    assert (O : OUTS f p).
    { apply snr_OUT. intros p' E'.
      destruct (Z_lt_le_dec (p_ol p) 1) as [L|L].
      - (* [comment removed for export] *)
        unfold S0F_bzd_snr1.HS. intros until rest. intros CHm SI Hf Hav.
        unfold S0F_bzd_snr1.sinv in SI. exfalso. lia.
      - destruct (IH (Z.to_nat (p_ol p')) ltac:(lia) p' eq_refl) as [H' _]. exact H'. }
    split; [| exact O]. apply snr_H; [apply G | exact O].
  Qed.

  (* [comment removed for export] *)
  Lemma snr_knot : forall f,
    (forall p, GS f p) /\ (forall p, HS f p) /\ (forall p, OUTS f p) /\ (forall p, MS_ f p).
  Proof.
    induction f as [|f IH].
    - assert (G : forall p, GS 0%nat p) by (intros p; apply (S0F_bzd_snr2.snr_G c OK OKS AL RD0 KJ KE); intros f' p' E; discriminate E).
      assert (HO : forall p, HS 0%nat p /\ OUTS 0%nat p) by (intros p; eapply (snr_HO 0%nat G); reflexivity).
      repeat split; try apply G; try (intros p; apply (proj1 (HO p))); try (intros p; apply (proj2 (HO p))).
      intros p. apply snr_M. apply (proj2 (HO p)).
    - cps_destruct IH as (G' & H' & O' & M').
      pose proof (S0F_bzd_snr4.snr_T5 c OK OKS AL RD0 f M') as T5.
      pose proof (S0F_bzd_snr4.snr_T4 c OK OKS AL RD0 KE f T5) as T4.
      pose proof (S0F_bzd_snr4.snr_T3 c OK OKS AL RD0 KE f T4 M') as T3.
      pose proof (S0F_bzd_snr3.snr_T2 c OK OKS AL RD0 KE f T3 M') as T2.
      pose proof (S0F_bzd_snr3.snr_T1 c OK OKS AL RD0 KE f T2 M') as T1.
      assert (G : forall p, GS (Datatypes.S f) p).
      { intros p; apply (S0F_bzd_snr2.snr_G c OK OKS AL RD0 KJ KE); intros f' p' E; injection E as <-; apply T1. }
      assert (HO : forall p, HS (Datatypes.S f) p /\ OUTS (Datatypes.S f) p) by (intros p; eapply (snr_HO _ G); reflexivity).
      repeat split; try apply G; try (intros p; apply (proj1 (HO p))); try (intros p; apply (proj2 (HO p))).
      intros p. apply snr_M. apply (proj2 (HO p)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem S0F_smallnr : forall (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
    DSg c m J d0 s0 -> DESTg c m s0 dbytes rest -> RO m -> munch WB m0 m -> wmono s0segs m0 m ->
    evt s0segs (KQ (unRLE d0 s0))
      (MS (RR ra t0 t1 t2 a0 cstrm (Z_to_bv 64 1) a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) F (Z_to_bv 64 0x1545c) fc None m (seg_rom s0segs)).
  Proof.
    intros until rest. intros DSm DE ROm MU WM.
    pose proof DSm as DSm0. pose proof DE as DE0.
    unDS DSm. cps_destruct DE as (DSTA & DL & Edb & Lout). unRO ROm. prep.
    assert (SMT : smallb d0 = true) by (unfold smallb; rewrite Esm, HSM; reflexivity).
    unfold id in NK0.
    rewrite (unRLE_plain d0 s0 (Z.to_nat (PP + 2 - d_nused d0))) by (first [rewrite SMT; reflexivity | lia]).
    cps_destruct (snr_knot (Z.to_nat (PP + 2 - d_nused d0))) as (_ & H1 & _ & _).
    remember (Z.to_nat (PP + 2 - d_nused d0)) as f eqn:Hf.
    set (p0 := PST (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0)
                   (s_out s0) (s_avail_out s0) (s_tout s0) (j_tol J) (j_toh J)).
    assert (ED : set8 d0 (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0) = d0) by apply set8_id.
    assert (ES : smod s0 (s_out s0) (s_avail_out s0) (s_tout s0) = s0) by apply smod_id.
    assert (EJ : jk_set_o J (j_tol J) (j_toh J) = J) by apply jk_set_o_id.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV.
    (* [comment removed for export] *)
    wstep; try notrap.
    wstep. try rewrite (sx32_of_Z (s_avail_out s0)) by lia.
    wstep. if_cases K0; zify_cond K0.
    - rewrite K_PM_ret by first [exact K0 | lia]. rewrite <- ED, <- ES. rewrite <- EJ in DSm0.
      eapply KJ; [exact DSm0 | exact DE0 | ro_close | exact MU | exact WM | ].
      unfold ojoin. focbn. repeat match goal with |- _ /\ _ => split end; first [lia | intros; exfalso; rewrite RD0 in *; lia | idtac].
    - rewrite K_PM_go by first [exact K0 | lia].
      pose proof (H1 p0) as H. unfold S0F_bzd_snr1.HS, S0F_bzd_snr1.CH in H. subst p0.
      unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in H. cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in H.
      rewrite ED, ES, EJ in H. try rewrite Eol0 in H.
      enter_with (H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [exact DSm0 | exact DE0 | ro_close | exact MU | exact WM]
        | unfold S0F_bzd_snr1.sinv; cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh];
          repeat match goal with |- _ /\ _ => split end; first [lia | reflexivity | exact Lout]
        | lia | lia ].
  Time Qed.
End SNR.

(* [comment removed for export] *)
Theorem S0F_smallnr_ok : SMALLNR_spec.
Proof.
  unfold SMALLNR_spec. intros c OK OKS AL KJ KE. intros until rest. intros DSm DE ROm MU WM RD0.
  eapply S0F_smallnr; eassumption.
Qed.
End ACeilS1.
