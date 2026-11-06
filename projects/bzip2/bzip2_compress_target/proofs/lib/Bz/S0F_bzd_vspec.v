(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables S0_bzd_out.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_out.

From Stdlib Require Wf_nat.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzLemmasT BzLemmasMtf BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_out S0F_bzd_fnr1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzImg0TacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SepFast RelLiaS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
Module S0F_bzd_fnr2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Arith.Wf_nat.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_bzd_out OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_out OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_fnr1.
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
Local Ltac BzSepTac.sep_tac ::= SepFast.sep_tac_u.
Local Ltac tlia ::= RelLiaS.tlia_bzd_r.
Local Ltac BzSepTac.tlia1 ::= RelLiaS.tlia1_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section FNR.
  Variable c : foctx.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation TT := (b_tt (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation RO := (FROf c). Notation WB := (FWB c).
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 :=
    (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 (b_s (o_cx c))) (o_s1v c) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (b_s (o_cx c) + 2047)) (Z_to_bv 64 (b_s (o_cx c) + 1096))
         (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 100000) (Z_to_bv 64 (b_s (o_cx c) + 64080)) s8 s9 (Z_to_bv 64 4) (Z_to_bv 64 10) t3 t4 t5 t6) (only parsing).
  Hypothesis OK : foctx_ok c. Hypothesis OKF : foctx_okF c.
  Hypothesis KJ : FKjoin c (FROf c).
  Hypothesis KE : FKexit c (FROf c).

  (* [comment removed for export] *)
  Notation KH1 := (K_H1 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KH2 := (K_H2 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KDR := (K_DR (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KG := (ucG (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation CC r := (ccommit (o_d c) (o_s c) r).

  Notation DESTc := (S0F_bzd_fnr1.DESTc c).
  Notation PS := (S0F_bzd_fnr1.PS c). Notation QS := (S0F_bzd_fnr1.QS c).
  Notation GS := (S0F_bzd_fnr1.GS c). Notation H2S := (S0F_bzd_fnr1.H2S c).
  Notation H1S := (S0F_bzd_fnr1.H1S c). Notation DRS := (S0F_bzd_fnr1.DRS c).
  Let fnr_ret := S0F_bzd_fnr1.fnr_ret c OK OKF KJ.
  Let fnr_G := S0F_bzd_fnr1.fnr_G c OK OKF KJ KE.
  Let KEc := S0F_bzd_fnr1.KEc c OK KE.

  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & TTA & CRC & RNA & GOT & MI); unfold FGOT in GOT.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  (* [comment removed for export] *)
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & SEP_SD & IAS & IAD & JWF & ENT);
    let OKF' := fresh "OKF" in pose proof OKF as OKF';
    cps_destruct OKF' as (HSM & HTT & SEP_ST & SEP_DT);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & _ & Rtt & _ & _);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold FWB in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length (d_tt d0) cap ltac:(lia)) as TTL; pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL; hide_disj.

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
  Ltac ro_close := unfold FROf, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.
  Ltac ojoin_close := unfold ojoin; focbn; repeat match goal with |- _ /\ _ => split end; first [lia | assumption | intros; lia | idtac].


  Notation csnb := (Z_to_bv 64 snb). Notation cpp := (Z_to_bv 64 (snb + 1)). Notation cnn := (Z_to_bv 64 (100000 * n)).
  Notation optr av := (Z_to_bv 64 (DST + (dlen - av))).
  Ltac cinv_close := unfold cinv; ccbv; cbn [length]; repeat match goal with |- _ /\ _ => split end; first [lia | mlia].

  (* [comment removed for export] *)
  Ltac dst_write av ch Edb RL :=
    let E' := ident:(E') in let R' := ident:(R') in lazymatch goal with DSTA : u8arr _ _ DST ?bs |- _ =>
      let SOK := fresh "SOK" in
      pose proof (u8arr_store_ok s0segs _ DST _ (dlen - av) _ DSTA ltac:(lia) eq_refl) as SOK;
      step; rewrite BzInv.le1_lit;
      let D := fresh "DSTB" in
      pose proof (u8arr_write s0segs _ DST _ (dlen - av) (Z_to_bv 8 ch) DSTA ltac:(lia)) as D;
      clear DSTA; store_done; try clear SOK; rename D into DSTA;
      lazymatch goal with DL : Z.of_nat (length bs) = _ |- _ =>
        let D2 := fresh "DLB" in
        pose proof DL as D2; rewrite <- (upd_length bs (Z.to_nat (dlen - av)) (Z_to_bv 8 ch)) in D2; clear DL; rename D2 into DL;
        unfold id in Edb;
        let r' := fresh "rest" in let E' := fresh "Edb" in let R' := fresh "RL" in
        cps_destruct (destc_snoc _ _ _ _ (Z.to_nat (dlen - av)) ch av Edb ltac:(rewrite length_map, length_rev; lia) RL ltac:(lia)) as (r' & E' & R');
        clear Edb RL; rename E' into Edb; rename R' into RL;
        let db := fresh "dbytes" in
        remember (upd bs (Z.to_nat (dlen - av)) (Z_to_bv 8 ch)) as db eqn:Xdb; clear Xdb;
        lazymatch type of Edb with ?x = ?y => change (id (x = y)) in Edb end
      end end.

  (* [comment removed for export] *)
  Ltac crc_step crc ch Hcrc :=
    let Hidx := fresh "Hidx" in
    pose proof (crc_idx_byte crc ch ltac:(lia) ltac:(lia)) as Hidx;
    wstep; wstep; wstep; wstep; rewrite Hcrc; wstep; wstep;
    lazymatch goal with CRC : u32arr _ ?mm 169656 crc_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read s0segs mm 169656 crc_words (Z.lxor (crc / 16777216) ch) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD;
      wstep; clear RD end.
  Ltac cc1 := lazymatch goal with |- evt _ (o_KQ c (ccommit _ _ (1%Z, ?X))) _ =>
    change (ccommit (o_d c) (o_s c) (1%Z, X)) with (1%Z, o_d c, o_s c) end.
  Ltac fix_optr av :=
    replace (Z_to_bv 64 (DST + (dlen - av) + 1)) with (Z_to_bv 64 (DST + (dlen - (av - 1)))) by (f_equal; lia).
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fnr_H2 : forall f cl, GS f (c_write cl) -> H2S f cl.
  Proof.
    intros f cl G. unfold S0F_bzd_fnr1.H2S, S0F_bzd_fnr1.PS. intros until rest. intros DSm DE ROm MU WM CI Hcrc Htp Hf.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSg in *. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM. ccbv_in G.
    rewrite K_H2_eq. ccbv.
    wstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq av 0)) by lia.
      wstep. wstep. wstep. wstep.
      enter_with (fnr_ret _ _ _ _ _ _ _ crcw tpw _ _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold S0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
        | ro_close | exact MU | exact WM
        | unfold cinv; ccbv; lia | ccbv; exact Hcrc | ccbv; exact Htp ].
    - rewrite (proj2 (Z.eqb_neq av 0)) by lia.
      dst_write av ch Edb RL.
      crc_step crc ch Hcrc.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. fix_optr av.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with DSTA : u8arr _ _ DST ?db |- _ => lazymatch type of RL with Z.of_nat (length ?r) = _ =>
          pose proof (crc_step_rel crcw crc ch Hcrc ltac:(lia) ltac:(lia)) as Hcrc';
          unfold S0F_bzd_fnr1.GS, S0F_bzd_fnr1.PS in G;
          enter_with (G _ _ _ _ _ _ tpw mm db r);
          [ ccbv; st_eq
          | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
          | unfold S0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
          | ro_close | exact MU | exact WM
          | pose proof (crc_update_range crc ch ltac:(lia)); cinv_close | ccbv; exact Hcrc' | ccbv; exact Htp | ccbv; lia ]
        end end end.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fnr_DR : forall f, (forall cl, H2S f cl) -> forall k cl, Z.to_nat (c_len cl) = k -> DRS f cl.
  Proof.
    intros f H2 k. induction k as [k IH] using lt_wf_ind. intros cl Hk.
    unfold S0F_bzd_fnr1.DRS, S0F_bzd_fnr1.QS. intros until rest. (intros DSm DE ROm MU WM CI Hcrc Htp Hf; cps_intros (Hl1 & Ha1 & ->)).
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSg in *. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM.
    (* [comment removed for export] *)
    wstep. wstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      rewrite K_DR_one by (ccbv; lia). rewrite <- K_H2_go by (ccbv; lia).
      wstep. wstep.
      pose proof (H2 (CLOC crc ch len nu k0 tp out av)) as H2c. unfold S0F_bzd_fnr1.H2S, S0F_bzd_fnr1.PS in H2c.
      enter_with (H2c _ _ _ _ _ crcw tpw _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold S0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
        | ro_close | exact MU | exact WM
        | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp | ccbv; lia ].
    - rewrite K_DR_step by (ccbv; lia). ccbv.
      dst_write av ch Edb RL.
      crc_step crc ch Hcrc.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. fix_optr av.
      pose proof (crc_step_rel crcw crc ch Hcrc ltac:(lia) ltac:(lia)) as Hcrc'.
      pose proof (crc_update_range crc ch ltac:(lia)) as CR'.
      wstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_eq (av - 1) 0)) by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          lazymatch goal with DSTA : u8arr _ _ DST ?db |- _ => lazymatch type of RL with Z.of_nat (length ?r) = _ =>
            enter_with (fnr_ret _ _ _ _ _ _ _ _ tpw mm _ db r);
            [ ccbv; st_eq
            | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
            | unfold S0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
            | ro_close | exact MU | exact WM
            | cinv_close | ccbv; exact Hcrc' | ccbv; exact Htp ]
          end end end.
      + rewrite (proj2 (Z.eqb_neq (av - 1) 0)) by lia.
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          lazymatch goal with DSTA : u8arr _ _ DST ?db |- _ => lazymatch type of RL with Z.of_nat (length ?r) = _ =>
            pose proof (IH (Z.to_nat (len - 1)) ltac:(lia) (CLOC (crc_update crc ch) ch (len - 1) nu k0 tp (ch :: out) (av - 1)) ltac:(reflexivity)) as DRc;
            unfold S0F_bzd_fnr1.DRS, S0F_bzd_fnr1.QS in DRc;
            enter_with (DRc _ _ _ _ _ _ tpw mm db r);
            [ ccbv; st_eq
            | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
            | unfold S0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
            | ro_close | exact MU | exact WM
            | cinv_close | ccbv; exact Hcrc' | ccbv; exact Htp | ccbv; lia | ccbv; repeat match goal with |- _ /\ _ => split end; [lia | lia | reflexivity] ]
          end end end.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fnr_H1 : forall f cl, GS f cl -> DRS f cl -> H1S f cl.
  Proof.
    intros f cl G DR. unfold S0F_bzd_fnr1.H1S, S0F_bzd_fnr1.QS. intros until rest. intros DSm DE ROm MU WM CI Hcrc Htp Hf _.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSg in *. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM.
    unfold S0F_bzd_fnr1.GS, S0F_bzd_fnr1.PS in G. unfold S0F_bzd_fnr1.DRS, S0F_bzd_fnr1.QS in DR.
    rewrite K_H1_eq. ccbv.
    wstep. if_cases KA; zify_cond KA; rewrite ?signed_lit_small in * by lia.
    - (* [comment removed for export] *)
      replace (0 <? len) with false by (symmetry; apply Z.ltb_ge; lia).
      wstep. wstep. wstep. wstep.
      enter_with (G _ _ _ _ _ crcw tpw _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold S0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
        | ro_close | exact MU | exact WM
        | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp | ccbv; lia ].
    - replace (0 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
      wstep. wstep. if_cases KB; zify_cond KB.
      + rewrite (proj2 (Z.eqb_eq av 0)) by lia.
        enter_with (fnr_ret _ _ _ _ _ _ _ crcw tpw _ _ dbytes rest);
          [ ccbv; st_eq
          | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
          | unfold S0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
          | ro_close | exact MU | exact WM
          | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp ].
      + rewrite (proj2 (Z.eqb_neq av 0)) by lia.
        enter_with (DR _ _ _ _ _ crcw tpw _ dbytes rest);
          [ ccbv; st_eq
          | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
          | unfold S0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
          | ro_close | exact MU | exact WM
          | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp | ccbv; lia | ccbv; repeat match goal with |- _ /\ _ => split end; [lia | lia | reflexivity] ].
  Time Qed.

  (* [comment removed for export] *)
  Lemma fnr_knot : forall f,
    (forall cl, GS f cl) /\ (forall cl, H2S f cl) /\ (forall cl, DRS f cl) /\ (forall cl, H1S f cl).
  Proof.
    induction f as [|f IH].
    - assert (G : forall cl, GS 0%nat cl) by (intros cl; apply fnr_G; intros f' cl' E; discriminate E).
      assert (H2 : forall cl, H2S 0%nat cl) by (intros cl; apply fnr_H2; apply G).
      assert (DR : forall cl, DRS 0%nat cl) by (intros cl; eapply (fnr_DR 0%nat H2); reflexivity).
      repeat split; try assumption. intros cl. apply fnr_H1; [apply G| apply DR].
    - cps_destruct IH as (G' & H2' & DR' & H1').
      assert (G : forall cl, GS (Datatypes.S f) cl).
      { intros cl; apply fnr_G; intros f' cl' E; injection E as <-; [apply H2'| apply H1']. }
      assert (H2 : forall cl, H2S (Datatypes.S f) cl) by (intros cl; apply fnr_H2; apply G).
      assert (DR : forall cl, DRS (Datatypes.S f) cl) by (intros cl; eapply (fnr_DR _ H2); reflexivity).
      repeat split; try assumption. intros cl. apply fnr_H1; [apply G| apply DR].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem S0F_fastnr : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
      (m : word -> option byte) (dbytes rest : list byte),
    DSg c m J d0 s0 -> DESTg c m s0 dbytes rest -> RO m -> munch WB m0 m -> wmono s0segs m0 m ->
    d_rand d0 = 0%Z ->
    evt s0segs (KQ (unRLE d0 s0)) (MS (RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6) F (Z_to_bv 64 0x151b4) fc None m (seg_rom s0segs)).
  Proof.
    intros until rest. intros DSm DE ROm MU WM RD0. unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & Lout). prep.
    assert (SMF : smallb d0 = false) by (unfold smallb; rewrite Esm, HSM; reflexivity).
    unfold id in NK0.
    assert (RL : Z.of_nat (length rest) = av0).
    { pose proof (f_equal (@length byte) Edb) as X. rewrite length_app, length_map, length_rev in X. lia. }
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ rest)) in Edb.
    rewrite (unRLE_creg d0 s0 (Z.to_nat (PP + 2 - d_nused d0)) SMF RD0) by lia.
    cps_destruct (fnr_knot (Z.to_nat (PP + 2 - d_nused d0))) as (_ & _ & _ & H1).
    remember (Z.to_nat (PP + 2 - d_nused d0)) as f eqn:Hf.
    unfold blk_cap.
    unfold DSg in *. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM. rewrite Eol0 in HD.
    pose proof (word_urange (sx32 (Z_to_bv 64 (d_tPos d0)))) as TPR.
    pose proof (sx32_mod32 (d_tPos d0) ltac:(lia)) as Htp.
    (* [comment removed for export] *)
    wstep. wstep. wstep. try rewrite (sx32_of_Z (d_nused d0)) by lia. wstep. wstep. wstep. try rewrite (sx32_of_Z 0) by lia.
    wstep. try rewrite (sx32_of_Z n) by lia. wstep. try rewrite (sx32_of_Z snb) by lia. wstep. wstep. try rewrite (sx32_of_Z av0) by lia.
    wstep. wstep. wstep. wstep. wstep.
    rewrite En. replace (Z_to_bv 64 (n * 100000)) with (Z_to_bv 64 (100000 * n)) by (f_equal; lia).
    replace (bv_unsigned (Z_to_bv 8 (d_out_ch d0))) with (d_out_ch d0)
      by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; cbn; lia).
    destruct NK0 as [[Hnu Hk0]|[Hnu Htp0]].
    - (* [comment removed for export] *)
      try rewrite (sx32_of_Z (d_k0 d0)) by lia.
      unfold S0F_bzd_fnr1.H1S, S0F_bzd_fnr1.QS in H1.
      enter_with (H1 (c0_of d0 s0) _ _ _ _ _ (sx32 (Z_to_bv 64 (d_cbcrc d0))) (sx32 (Z_to_bv 64 (d_tPos d0))) _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSg; dvF_cbn; rewrite Eol0; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold S0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end;
            [exact DSTA| exact DL| unfold id in Edb; rewrite Edb; reflexivity| exact RL]
        | ro_close | exact MU | exact WM
        | cinv_close | ccbv; apply sx32_mod32; lia | ccbv; exact Htp | ccbv; lia | exact I ].
    - (* [comment removed for export] *)
      rewrite K_H1_eq. ccbv. rewrite Eol0. replace (0 <? 0)%Z with false by reflexivity. cbv beta iota.
      rewrite ucG_go by (ccbv; lia). rewrite G1_None by (ccbv; lia). cc1.
      (* [comment removed for export] *)
      wstep. if_cases KA; zify_cond KA; rewrite ?signed_lit_small in * by lia; [| exfalso; lia].
      wstep. wstep. wstep. wstep. wstep.
      wstep. if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia; [exfalso; lia|].
      wstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      wstep. wstep. if_cases K3; zify_cond K3.
      2:{ exfalso. destruct (sextw_lt (bv_unsigned (sx32 (Z_to_bv 64 (d_tPos d0)))) cap (proj1 TPR) ltac:(lia) K3) as [LT _].
          change (2^32)%Z with 4294967296%Z in LT. rewrite Htp in LT. lia. }
      unfold id in Edb.
      eapply (KEc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] dbytes rest);
        [unfold DSg; dvF_cbn; rewrite Eol0; repeat match goal with |- _ /\ _ => split end; assumption
        | exact DSTA| exact DL| rewrite Edb; reflexivity | ro_close | exact MU | exact WM].
  Time Qed.
End FNR.
End ACeilS1.
End S0F_bzd_fnr2.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_out OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_bzd_vspec.S0F_bzd_fnr2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition FASTR_spec : Prop :=
    forall c : foctx, foctx_ok c -> foctx_okF c -> FKjoin c (FROf c) -> FKexit c (FROf c) ->
    forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      DSg c m (o_J c) (o_d c) (o_s c) -> DESTg c m (o_s c) dbytes rest -> FROf c m ->
      munch (FWB c) (o_m0 c) m -> wmono s0segs (o_m0 c) m ->
      d_rand (o_d c) = 1%Z ->
      evt s0segs (o_KQ c (unRLE (o_d c) (o_s c)))
          (MS (FRR c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 14) (Z_to_bv 64 3) t3 t4 t5 t6) (o_F c) (Z_to_bv 64 0x14b04) (o_fc c) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Definition SMALLNR_spec : Prop :=
    forall c : foctx, foctx_ok c -> foctx_okS c -> FKjoin c (FROs c) -> FKexit c (FROs c) ->
    forall (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      DSg c m (o_J c) (o_d c) (o_s c) -> DESTg c m (o_s c) dbytes rest -> FROs c m ->
      munch (FWB c) (o_m0 c) m -> wmono s0segs (o_m0 c) m ->
      d_rand (o_d c) = 0%Z ->
      evt s0segs (o_KQ c (unRLE (o_d c) (o_s c)))
          (MS (FRR c ra t0 t1 t2 a0 (Z_to_bv 64 (b_strm (o_cx c))) (Z_to_bv 64 (s_avail_out (o_s c))) a3 a4 a5 a6 a7 (Z_to_bv 64 14) (Z_to_bv 64 3) t3 t4 t5 t6)
              (o_F c) (Z_to_bv 64 0x14e48) (o_fc c) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Definition SMALLR_spec : Prop :=
    forall c : foctx, foctx_ok c -> foctx_okS c -> FKjoin c (FROs c) -> FKexit c (FROs c) ->
    forall (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
      DSg c m (o_J c) (o_d c) (o_s c) -> DESTg c m (o_s c) dbytes rest -> FROs c m ->
      munch (FWB c) (o_m0 c) m -> wmono s0segs (o_m0 c) m ->
      d_rand (o_d c) = 1%Z ->
      evt s0segs (o_KQ c (unRLE (o_d c) (o_s c)))
          (MS (FRR c ra t0 t1 t2 a0 (Z_to_bv 64 (b_strm (o_cx c))) (Z_to_bv 64 (s_avail_out (o_s c))) a3 a4 a5 a6 a7 (Z_to_bv 64 14) (Z_to_bv 64 3) t3 t4 t5 t6)
              (o_F c) (Z_to_bv 64 0x1461c) (o_fc c) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
End ACeilS1.
