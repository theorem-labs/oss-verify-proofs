(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzWalkArith BzWalkArith2 S0_bzd_out BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDOKS DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_out S0F_bzd_outS S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_outR S0F_bzd_snr1 S0F_bzd_vspec S0F_bzd_sr1.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_out S0F_bzd_outS S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_outR S0F_bzd_snr1 S0F_bzd_sr1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzImg0TacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLiaS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
Module S0F_bzd_sr2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Arith.Wf_nat.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_bzd_out OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_out OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_outS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_fr1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_fr2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_outR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_snr1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr1.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzImg0TacF.
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
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 :=
    (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 (b_s (o_cx c))) (o_s1v c) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (b_s (o_cx c) + 2047)) (Z_to_bv 64 (b_s (o_cx c) + 1096))
         (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 100000) (Z_to_bv 64 (b_s (o_cx c) + 64080)) s8 s9 (Z_to_bv 64 4) (Z_to_bv 64 10) t3 t4 t5 t6) (only parsing).
  Hypothesis OK : foctx_ok c. Hypothesis OKS : foctx_okS c. Hypothesis RD1 : d_rand (o_d c) = 1%Z.
  Hypothesis KJ : FKjoin c (FROs c).
  Hypothesis KE : FKexit c (FROs c).

  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation CH := (S0F_bzd_snr1.CH c). Notation sinvR := (S0F_bzd_sr1.sinvR c). Notation DR := (S0F_bzd_sr1.DR c).
  Notation MS_ := (S0F_bzd_sr1.MS_ c). Notation HS := (S0F_bzd_sr1.HS c). Notation OUTS := (S0F_bzd_sr1.OUTS c).
  Notation GS := (S0F_bzd_sr1.GS c).
  Notation T1S := (S0F_bzd_sr1.T1S c). Notation T2S := (S0F_bzd_sr1.T2S c). Notation T3S := (S0F_bzd_sr1.T3S c).
  Notation T4S := (S0F_bzd_sr1.T4S c). Notation T5S := (S0F_bzd_sr1.T5S c).
  Notation R1S := (S0F_bzd_sr1.R1S c). Notation R2S := (S0F_bzd_sr1.R2S c). Notation R3S := (S0F_bzd_sr1.R3S c).
  Notation R4S := (S0F_bzd_sr1.R4S c). Notation R5S := (S0F_bzd_sr1.R5S c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation csnb := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)))).
  Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)).
  Notation c14 := (Z_to_bv 64 14). Notation c3 := (Z_to_bv 64 3). Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).

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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_G : forall f, (forall f' p', f = Datatypes.S f' -> T1S f' p') -> forall p, GS f p.
  Proof.
    intros f IHT1 p. unfold S0F_bzd_sr1.GS. intros until rest. intros CHm SI Hf Hav Hol.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst ol.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z snb) by lia. wstep. try rewrite (sx32_of_Z nu) by lia. wstep.
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      rewrite K_PG_done by (s8; lia).
      eapply KJ; [dsg_close | destg_close | ro_close | exact MU | exact WM | ojoin_close]. }
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
        eapply (S0F_bzd_sr1.sr_B1 c OK OKS P mm tp) with (k := 7%nat) (t := 0%nat); [ro_close | lia | | reflexivity | reflexivity] end.
      intros t1' t3' lo hi E8.
      pose proof (iif_result cf tp lo hi E8) as RES.
      spec_cut (IHT1 f') S0F_bzd_sr1.T1S (PST k0 1 nu k0 tp rn rt cb out av tout tol toh) T1. specialize (T1 eq_refl).
      rewrite <- RES.
      enter_with (T1 _ _ _ _ _ _ _ _ _ dbytes rest);
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
End SR.
End ACeilS1.
End S0F_bzd_sr2.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_sr6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_sr6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_sr6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_sr6.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_out OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_outS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_fr1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_fr2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_outR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_snr1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_vspec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr7.S0F_bzd_sr2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr6.S0F_bzd_sr3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr6.S0F_bzd_sr4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr6.S0F_bzd_sr5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr6.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.
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
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 :=
    (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 (b_s (o_cx c))) (o_s1v c) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (b_s (o_cx c) + 2047)) (Z_to_bv 64 (b_s (o_cx c) + 1096))
         (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 100000) (Z_to_bv 64 (b_s (o_cx c) + 64080)) s8 s9 (Z_to_bv 64 4) (Z_to_bv 64 10) t3 t4 t5 t6) (only parsing).
  Hypothesis OK : foctx_ok c. Hypothesis OKS : foctx_okS c. Hypothesis RD1 : d_rand (o_d c) = 1%Z.
  Hypothesis KJ : FKjoin c (FROs c).
  Hypothesis KE : FKexit c (FROs c).

  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation CH := (S0F_bzd_snr1.CH c). Notation sinvR := (S0F_bzd_sr1.sinvR c). Notation DR := (S0F_bzd_sr1.DR c).
  Notation MS_ := (S0F_bzd_sr1.MS_ c). Notation HS := (S0F_bzd_sr1.HS c). Notation OUTS := (S0F_bzd_sr1.OUTS c).
  Notation GS := (S0F_bzd_sr1.GS c).
  Notation T1S := (S0F_bzd_sr1.T1S c). Notation T2S := (S0F_bzd_sr1.T2S c). Notation T3S := (S0F_bzd_sr1.T3S c).
  Notation T4S := (S0F_bzd_sr1.T4S c). Notation T5S := (S0F_bzd_sr1.T5S c).
  Notation R1S := (S0F_bzd_sr1.R1S c). Notation R2S := (S0F_bzd_sr1.R2S c). Notation R3S := (S0F_bzd_sr1.R3S c).
  Notation R4S := (S0F_bzd_sr1.R4S c). Notation R5S := (S0F_bzd_sr1.R5S c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation csnb := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)))).
  Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)).
  Notation c14 := (Z_to_bv 64 14). Notation c3 := (Z_to_bv 64 3). Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).

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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
    lazymatch goal with CRC : u32arr _ ?mm 169656 crc_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read s0segs mm 169656 crc_words (Z.lxor (crc / 16777216) ch) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD;
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


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_OUT : forall f p,
    (forall p', p_ol p' = (p_ol p - 1)%Z -> HS f p') -> OUTS f p.
  Proof.
    intros f p IHH. unfold S0F_bzd_sr1.OUTS. intros until rest. intros CHm SI Hf Hav Hol.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    rewrite K_PH_step by (s8; lia). cbv zeta. s8.
    pose proof (sx32_mod32 cb ltac:(lia)) as Hcrc.
    (* [comment removed for export] *)
    wstep. rewrite zxb_lit8 by lia. wstep.
    (* [comment removed for export] *)
    dst_write av oc.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. rewrite Hcrc. wstep. wstep. wstep.
    (* [comment removed for export] *)
    crc_load cb oc.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    pose proof (crc_step_rel (sx32 (Z_to_bv 64 cb)) cb oc Hcrc ltac:(lia) ltac:(lia)) as Hcrc'.
    pose proof (crc_update_range cb oc ltac:(lia)) as CR'.
    (* [comment removed for export] *)
    wstep.
    let crcw := reg_val 12%Z in recell MID crcw (crc_update cb oc); [| rewrite Hcrc'; symmetry; apply Z.mod_small; lia].
    (* [comment removed for export] *)
    wstep. wstep. try rewrite (sx32_of_Z av) by lia. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    replace (DST + (dlen - av) + 1)%Z with (DST + (dlen - (av - 1)))%Z in SM by lia.
    (* [comment removed for export] *)
    Ltac fin IHH MU WM oc ol nu k0 tp rn rt cb out av tout :=
      let KA := fresh "KA" in
      wstep; if_cases KA; zify_cond KA;
      [ (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_eq (av - 1) 0)) by lia;
        eapply KJ; [dsg_close | destg_close | ro_close | exact MU | exact WM | ojoin_close ]
      | rewrite (proj2 (Z.eqb_neq (av - 1) 0)) by lia;
        wstep;
        enter_with (IHH (PST oc (ol - 1) nu k0 tp rn rt (crc_update cb oc) (oc :: out) (av - 1) (tout + 1) _ _) eq_refl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [ cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh]; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss; st_eq
        | unfold S0F_bzd_snr1.CH; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp;
          cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh];
          repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | ro_close | exact MU | exact WM]
        | sinv_close
        | cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh]; lia
        | cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh]; lia ] ].
    wstep. if_cases KT; zify_cond KT.
    - fin IHH MU WM oc ol nu k0 tp rn rt cb out av tout.
    - wstep. wstep. wstep. fin IHH MU WM oc ol nu k0 tp rn rt cb out av tout.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_H : forall f p, GS f p -> OUTS f p -> HS f p.
  Proof.
    intros f p G O. unfold S0F_bzd_sr1.HS. intros until rest. intros CHm SI Hf Hav.
    pose proof CHm as CH0. pose proof SI as SI0.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold S0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_sr1.sinvR in CHm, SI, Hf, Hav |- *.
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in *.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep.
    (* [comment removed for export] *)
    wstep. if_cases K0; zify_cond K0.
    - unfold S0F_bzd_sr1.OUTS in O. eapply O; [exact CH0 | exact SI0 | cbn [p_nu]; lia | cbn [p_av]; lia | cbn [p_ol]; lia].
    - rewrite K_PH_0 by (s8; lia). unfold S0F_bzd_sr1.GS in G. eapply G; [exact CH0 | exact SI0 | cbn [p_nu]; lia | cbn [p_av]; lia | cbn [p_ol]; lia].
  Time Qed.

  Lemma sr_M : forall f p, OUTS f p -> MS_ f p.
  Proof.
    intros f p O. unfold S0F_bzd_sr1.MS_. intros until rest. intros CHm SI Hf Hol.
    pose proof CHm as CH0. pose proof SI as SI0.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold S0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_sr1.sinvR in CHm, SI, Hf, Hol |- *.
    cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in *.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z av) by lia.
    wstep. if_cases K0; zify_cond K0.
    - rewrite K_PM_ret by (s8; lia).
      eapply KJ; [dsg_close | destg_close | ro_close | exact MU | exact WM | ojoin_close].
    - rewrite K_PM_go by (s8; lia).
      unfold S0F_bzd_sr1.OUTS in O. eapply O; [exact CH0 | exact SI0 | cbn [p_nu]; lia | cbn [p_av]; lia | cbn [p_ol]; lia].
  Time Qed.

  (* [comment removed for export] *)
  Lemma sr_HO : forall f, (forall p, GS f p) -> forall k p, Z.to_nat (p_ol p) = k -> HS f p /\ OUTS f p.
  Proof.
    intros f G k. induction k as [k IH] using lt_wf_ind. intros p Hk.
    assert (O : OUTS f p).
    { apply sr_OUT. intros p' E'.
      destruct (Z_lt_le_dec (p_ol p) 1) as [L|L].
      - unfold S0F_bzd_sr1.HS. intros until rest. intros CHm SI Hf Hav.
        unfold S0F_bzd_sr1.sinvR in SI. exfalso. lia.
      - destruct (IH (Z.to_nat (p_ol p')) ltac:(lia) p' eq_refl) as [H' _]. exact H'. }
    split; [| exact O]. apply sr_H; [apply G | exact O].
  Qed.

  (* [comment removed for export] *)
  Ltac hyps := first [exact OK | exact OKS | exact RD1 | exact KJ | exact KE].
  Lemma sr_knot : forall f,
    (forall p, GS f p) /\ (forall p, HS f p) /\ (forall p, OUTS f p) /\ (forall p, MS_ f p).
  Proof.
    induction f as [|f IH].
    - assert (G : forall p, GS 0%nat p).
      { intros p. eapply S0F_bzd_sr2.sr_G; try hyps. intros f' p' E; discriminate E. }
      assert (HO : forall p, HS 0%nat p /\ OUTS 0%nat p) by (intros p; eapply (sr_HO 0%nat G); reflexivity).
      repeat split; try apply G; try (intros p; apply (proj1 (HO p))); try (intros p; apply (proj2 (HO p))).
      intros p. apply sr_M. apply (proj2 (HO p)).
    - cps_destruct IH as (G' & H' & O' & M').
      assert (R5 : forall p, R5S f p) by (intros p; eapply S0F_bzd_sr6.sr_R5; try hyps; exact M').
      assert (T5 : forall p, T5S f p) by (intros p; eapply S0F_bzd_sr6.sr_T5; try hyps; exact R5).
      assert (R4 : forall p, R4S f p) by (intros p; eapply S0F_bzd_sr6.sr_R4; try hyps; exact T5).
      assert (T4 : forall p, T4S f p) by (intros p; eapply S0F_bzd_sr6.sr_T4; try hyps; exact R4).
      assert (R3 : forall p, R3S f p) by (intros p; eapply OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr6.S0F_bzd_sr5.sr_R3; try hyps; [exact T4 | exact M']).
      assert (T3 : forall p, T3S f p) by (intros p; eapply OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr6.S0F_bzd_sr5.sr_T3; try hyps; exact R3).
      assert (R2 : forall p, R2S f p) by (intros p; eapply OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr6.S0F_bzd_sr4.sr_R2; try hyps; [exact T3 | exact M']).
      assert (T2 : forall p, T2S f p) by (intros p; eapply OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr6.S0F_bzd_sr4.sr_T2; try hyps; exact R2).
      assert (R1 : forall p, R1S f p) by (intros p; eapply OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr6.S0F_bzd_sr3.sr_R1; try hyps; [exact T2 | exact M']).
      assert (T1 : forall p, T1S f p) by (intros p; eapply OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_sr6.S0F_bzd_sr3.sr_T1; try hyps; exact R1).
      assert (G : forall p, GS (Datatypes.S f) p).
      { intros p. eapply S0F_bzd_sr2.sr_G; try hyps. intros f' p' E; injection E as <-; apply T1. }
      assert (HO : forall p, HS (Datatypes.S f) p /\ OUTS (Datatypes.S f) p) by (intros p; eapply (sr_HO _ G); reflexivity).
      repeat split; try apply G; try (intros p; apply (proj1 (HO p))); try (intros p; apply (proj2 (HO p))).
      intros p. apply sr_M. apply (proj2 (HO p)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem S0F_smallr : forall (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
    DSg c m J d0 s0 -> DESTg c m s0 dbytes rest -> RO m -> munch WB m0 m -> wmono s0segs m0 m ->
    evt s0segs (KQ (unRLE d0 s0))
      (MS (RR ra t0 t1 t2 a0 cstrm (Z_to_bv 64 (s_avail_out s0)) a3 a4 a5 a6 a7 c14 c3 t3 t4 t5 t6) F (Z_to_bv 64 0x1461c) fc None m (seg_rom s0segs)).
  Proof.
    intros until rest. intros DSm DE ROm MU WM.
    pose proof DSm as DSm0. pose proof DE as DE0.
    unDS DSm. cps_destruct DE as (DSTA & DL & Edb & Lout). unRO ROm. prep.
    assert (SMT : smallb d0 = true) by (unfold smallb; rewrite Esm, HSM; reflexivity).
    unfold id in NK0. pose proof (Rrnd RD1) as [RrN0 RrT0].
    rewrite (unRLE_plain d0 s0 (Z.to_nat (PP + 2 - d_nused d0))) by (first [rewrite SMT; reflexivity | lia]).
    cps_destruct (sr_knot (Z.to_nat (PP + 2 - d_nused d0))) as (_ & H1 & _ & _).
    remember (Z.to_nat (PP + 2 - d_nused d0)) as f eqn:Hf.
    set (p0 := PST (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0)
                   (s_out s0) (s_avail_out s0) (s_tout s0) (j_tol J) (j_toh J)).
    assert (ED : set8 d0 (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0) = d0) by apply set8_id.
    assert (ES : smod s0 (s_out s0) (s_avail_out s0) (s_tout s0) = s0) by apply smod_id.
    assert (EJ : jk_set_o J (j_tol J) (j_toh J) = J) by apply jk_set_o_id.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV.
    (* [comment removed for export] *)
    wstep. if_cases K0; zify_cond K0.
    - rewrite K_PM_ret by exact K0. rewrite <- ED, <- ES. rewrite <- EJ in DSm0.
      eapply KJ; [exact DSm0 | exact DE0 | ro_close | exact MU | exact WM | ].
      unfold ojoin. focbn. repeat match goal with |- _ /\ _ => split end; first [lia | intros; lia | idtac].
    - rewrite K_PM_go by exact K0.
      (* [comment removed for export] *)
      wstep. rewrite Eol0. try rewrite (sx32_of_Z 0) by lia.
      pose proof (H1 p0) as H. unfold S0F_bzd_sr1.HS, S0F_bzd_snr1.CH in H. subst p0.
      unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in H. cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh] in H.
      rewrite ED, ES, EJ, Eol0 in H.
      enter_with (H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq
        | repeat match goal with |- _ /\ _ => split end; [exact DSm0 | exact DE0 | ro_close | exact MU | exact WM]
        | unfold S0F_bzd_sr1.sinvR; cbn [p_oc p_ol p_nu p_k0 p_tp p_rn p_rt p_cb p_out p_av p_tout p_tol p_toh];
          repeat match goal with |- _ /\ _ => split end; first [lia | reflexivity | exact Lout]
        | lia | lia ].
  Time Qed.
End SR.

(* [comment removed for export] *)
Theorem S0F_smallr_ok : SMALLR_spec.
Proof.
  unfold SMALLR_spec. intros c OK OKS KJ KE. intros until rest. intros DSm DE ROm MU WM RD1.
  eapply (S0F_smallr c OK OKS RD1 KJ KE); eassumption.
Qed.
End ACeilS1.
