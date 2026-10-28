(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzLemmasT BzLemmasMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0_bzd_out. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_out.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit S0F_bzd_fnr1.
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

Section FNR.
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
  Hypothesis OK : foctx_ok c. Hypothesis OKF : foctx_okF c. Hypothesis AL : foctx_al c.
  Hypothesis KJ : FKjoin c (FROf c).
  Hypothesis KE : FKexit c (FROf c).

  Notation KH1 := (K_H1 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KH2 := (K_H2 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KDR := (K_DR (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KG := (ucG (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation CC r := (ccommit (o_d c) (o_s c) r).
  Notation cTT := (Z_to_bv 64 (b_tt (o_cx c))).
  Notation cNT := (Z_to_bv 64 (18446744073709551615 - b_tt (o_cx c))).
  Notation cPP := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)) + 1)).
  Notation cCAP := (Z_to_bv 64 (100000 * b_n (o_cx c))).
  Notation optr av := (Z_to_bv 64 (DST + (dlen - av))).

  Notation DESTc := (S0F_bzd_fnr1.DESTc c).
  Notation GS := (S0F_bzd_fnr1.GS c). Notation H2S := (S0F_bzd_fnr1.H2S c).
  Notation H1S := (S0F_bzd_fnr1.H1S c). Notation DRS := (S0F_bzd_fnr1.DRS c).
  Let fnr_ret := S0F_bzd_fnr1.fnr_ret c OK OKF AL KJ KE.
  Let fnr_G := S0F_bzd_fnr1.fnr_G c OK OKF AL KJ KE.
  Let KEc := S0F_bzd_fnr1.KEc c OK OKF AL KJ KE.

  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & TTA & CRC & RNA & GOT & MI); unfold FGOT in GOT.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & SEP_SD & IAS & IAD & JWF & ENT);
    let OKF' := fresh "OKF" in pose proof OKF as OKF';
    cps_destruct OKF' as (HSM & HTT & SEP_ST & SEP_DT);
    let AL' := fresh "AL" in pose proof AL as AL'; unfold foctx_al, ctx_al in AL';
    let AL1 := fresh "AL" in destruct AL' as [AL1 ALstrm]; cps_destruct AL1 as (ALs & ALsp & ALsrc & ALdst & ALtt & ALl16 & ALl4);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & _ & Rtt & _ & _);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold FWB in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length (d_tt d0) cap ltac:(lia)) as TTL; pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL; hide_disj.
  Ltac ro_close := unfold FROf, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.
  Ltac cinv_close := unfold cinv; ccbv; cbn [length]; repeat match goal with |- _ /\ _ => split end; first [lia | mlia].

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
  Ltac cc1 := lazymatch goal with |- evt _ (o_KQ c (ccommit _ _ (1%Z, ?X))) _ =>
    change (ccommit (o_d c) (o_s c) (1%Z, X)) with (1%Z, o_d c, o_s c) end.
  Ltac fix_optr av :=
    replace (Z_to_bv 64 (DST + (dlen - av) + 1)) with (Z_to_bv 64 (DST + (dlen - (av - 1)))) by (f_equal; lia).

  Lemma fnr_H2 : forall f cl, GS f (c_write cl) -> H2S f cl.
  Proof using OK OKF AL KJ KE.
    intros f cl G. unfold S0F_bzd_fnr1.H2S. intros until rest. intros DSm DE ROm MU WM CI Hcrc Htp Hf.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSg in *. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM. ccbv_in G.
    rewrite K_H2_eq. ccbv.
    urun. if_cases K0; zify_cond K0.
    - rewrite (proj2 (Z.eqb_eq av 0)) by lia.
      urun_to 0x15bc8%Z.
      enter_with (fnr_ret _ _ _ _ _ _ _ _ _ crcw tpw _ _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
        | ro_close | exact MU | exact WM
        | unfold cinv; ccbv; lia | ccbv; exact Hcrc | ccbv; exact Htp ].
    - rewrite (proj2 (Z.eqb_neq av 0)) by lia.
      pose proof (crc_idx_byte crc ch ltac:(lia) ltac:(lia)) as Hidx.
      urun_to 0x15a20%Z.
      rewrite Hcrc.
      dst_write av ch Edb RL.
      urun.
      lazymatch goal with CRC : u32arr _ ?mm 0x33178 crc_words |- _ =>
        let RD := fresh "RD" in
        pose proof (u32arr_read s0segs mm 0x33178 crc_words (Z.lxor (crc / 16777216) ch) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD;
        wstep; clear RD end.
      urun_to 0x15a44%Z. fix_optr av.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with DSTA : u8arr _ _ DST ?db |- _ => lazymatch type of RL with Z.of_nat (length ?r) = _ =>
          pose proof (crc_step_rel crcw crc ch Hcrc ltac:(lia) ltac:(lia)) as Hcrc';
          unfold S0F_bzd_fnr1.GS in G;
          enter_with (G _ _ _ _ _ _ _ _ tpw mm db r);
          [ ccbv; st_eq
          | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
          | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
          | ro_close | exact MU | exact WM
          | pose proof (crc_update_range crc ch ltac:(lia)); cinv_close | ccbv; exact Hcrc' | ccbv; exact Htp | ccbv; lia ]
        end end end.
  Qed.


  Lemma fnr_DR : forall f, (forall cl, H2S f cl) -> forall k cl, Z.to_nat (c_len cl) = k -> DRS f cl.
  Proof using OK OKF AL KJ KE.
    intros f H2 k. induction k as [k IH] using lt_wf_ind. intros cl Hk.
    unfold S0F_bzd_fnr1.DRS. intros until rest. intros DSm DE ROm MU WM CI Hcrc Htp Hf Hl1 Ha1 Hj0 Hja Hjl.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSg in *. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM.
    urun. if_cases K0; zify_cond K0.
    - rewrite K_DR_one by (ccbv; lia). rewrite <- K_H2_go by (ccbv; lia).
      urun_to 0x15a00%Z.
      pose proof (H2 (CLOC crc ch len nu k0 tp out av)) as H2c. unfold S0F_bzd_fnr1.H2S in H2c.
      enter_with (H2c _ _ _ _ _ _ _ crcw tpw _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
        | ro_close | exact MU | exact WM
        | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp | ccbv; lia ].
    - rewrite K_DR_step by (ccbv; lia). ccbv.
      pose proof (crc_idx_byte crc ch ltac:(lia) ltac:(lia)) as Hidx.
      urun_to 0x159b4%Z.
      dst_write av ch Edb RL.
      urun.
      rewrite Hcrc.
      lazymatch goal with CRC : u32arr _ ?mm 0x33178 crc_words |- _ =>
        let RD := fresh "RD" in
        pose proof (u32arr_read s0segs mm 0x33178 crc_words (Z.lxor (crc / 16777216) ch) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD;
        wstep; clear RD end.
      pose proof (crc_step_rel crcw crc ch Hcrc ltac:(lia) ltac:(lia)) as Hcrc'.
      pose proof (crc_update_range crc ch ltac:(lia)) as CR'.
      urun. if_cases K1; zify_cond K1.
      + rewrite (proj2 (Z.eqb_neq (av - 1) 0)) by lia.
        urun_to 0x159ac%Z. fix_optr av.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          lazymatch goal with DSTA : u8arr _ _ DST ?db |- _ => lazymatch type of RL with Z.of_nat (length ?r) = _ =>
            pose proof (IH (Z.to_nat (len - 1)) ltac:(lia) (CLOC (crc_update crc ch) ch (len - 1) nu k0 tp (ch :: out) (av - 1)) ltac:(reflexivity)) as DRc;
            unfold S0F_bzd_fnr1.DRS in DRc;
            enter_with (DRc _ _ _ _ tpw (j + 1)%Z mm db r);
            [ ccbv; st_eq
            | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
            | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
            | ro_close | exact MU | exact WM
            | cinv_close | ccbv; exact Hcrc' | ccbv; exact Htp | ccbv; lia | ccbv; lia | ccbv; lia | lia | ccbv; lia | ccbv; lia ]
          end end end.
      + rewrite (proj2 (Z.eqb_eq (av - 1) 0)) by lia.
        urun_to 0x15bc8%Z. fix_optr av.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          lazymatch goal with DSTA : u8arr _ _ DST ?db |- _ => lazymatch type of RL with Z.of_nat (length ?r) = _ =>
            enter_with (fnr_ret _ _ _ _ _ _ _ _ _ _ tpw mm _ db r);
            [ ccbv; st_eq
            | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
            | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
            | ro_close | exact MU | exact WM
            | cinv_close | ccbv; exact Hcrc' | ccbv; exact Htp ]
          end end end.
  Qed.

  Lemma fnr_H1 : forall f cl, GS f cl -> DRS f cl -> H1S f cl.
  Proof using OK OKF AL KJ KE.
    intros f cl G DR. unfold S0F_bzd_fnr1.H1S. intros until rest. intros DSm DE ROm MU WM CI Hcrc Htp Hf.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSg in *. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM.
    unfold S0F_bzd_fnr1.GS in G. unfold S0F_bzd_fnr1.DRS in DR.
    rewrite K_H1_eq. ccbv.
    urun. if_cases KA; zify_cond KA; rewrite ?signed_lit_small in * by lia.
    - replace (0 <? len) with false by (symmetry; apply Z.ltb_ge; lia).
      urun_to 0x15a44%Z.
      enter_with (G _ _ _ _ _ _ _ crcw tpw _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
        | ro_close | exact MU | exact WM
        | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp | ccbv; lia ].
    - replace (0 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
      urun. if_cases KB; zify_cond KB.
      + rewrite (proj2 (Z.eqb_eq av 0)) by lia.
        urun_to 0x15bc8%Z.
        enter_with (fnr_ret _ _ _ _ _ _ _ _ _ crcw tpw _ _ dbytes rest);
          [ ccbv; st_eq
          | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
          | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
          | ro_close | exact MU | exact WM
          | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp ].
      + rewrite (proj2 (Z.eqb_neq av 0)) by lia.
        urun_to 0x159ac%Z.
        enter_with (DR _ _ _ crcw tpw 0%Z _ dbytes rest);
          [ ccbv; st_eq
          | unfold DSg; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
          | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
          | ro_close | exact MU | exact WM
          | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp | ccbv; lia | ccbv; lia | ccbv; lia | lia | ccbv; lia | ccbv; lia ].
  Qed.

  Lemma fnr_knot : forall f,
    (forall cl, GS f cl) /\ (forall cl, H2S f cl) /\ (forall cl, DRS f cl) /\ (forall cl, H1S f cl).
  Proof using OK OKF AL KJ KE.
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

  Theorem S0F_fastnr : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word)
      (m : word -> option byte) (dbytes rest : list byte),
    DSg c m (o_J c) (o_d c) (o_s c) -> DESTg c m (o_s c) dbytes rest -> FROf c m -> munch (FWB c) (o_m0 c) m ->
    wmono s0segs (o_m0 c) m -> d_rand (o_d c) = 0%Z ->
    evt s0segs (o_KQ c (unRLE (o_d c) (o_s c)))
      (MS (FRR c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6) (o_F c) (Z_to_bv 64 0x15944) (o_fc c) None m (seg_rom s0segs)).
  Proof using OK OKF AL KJ KE.
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
    urun_to 0x15994%Z.
    rewrite En. replace (Z_to_bv 64 (n * 100000)) with (Z_to_bv 64 (100000 * n)) by (f_equal; lia).
    replace (bv_unsigned (Z_to_bv 8 (d_out_ch d0))) with (d_out_ch d0)
      by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; cbn; lia).
    destruct NK0 as [[Hnu Hk0]|[Hnu Htp0]].
    - try rewrite (sx32_of_Z (d_k0 d0)) by lia.
      unfold S0F_bzd_fnr1.H1S in H1.
      enter_with (H1 (c0_of d0 s0) _ _ _ _ _ _ (sx32 (Z_to_bv 64 (d_cbcrc d0))) (sx32 (Z_to_bv 64 (d_tPos d0))) _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSg; dvF_cbn; rewrite Eol0; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold DESTc; ccbv; repeat match goal with |- _ /\ _ => split end;
            [exact DSTA| exact DL| unfold id in Edb; rewrite Edb; reflexivity| exact RL]
        | ro_close | exact MU | exact WM
        | cinv_close | ccbv; apply sx32_mod32; lia | ccbv; exact Htp | ccbv; lia ].
    - rewrite K_H1_eq. ccbv. rewrite Eol0. replace (0 <? 0)%Z with false by reflexivity. cbv beta iota.
      rewrite ucG_go by (ccbv; lia). rewrite G1_None by (ccbv; lia). cc1.
      urun.
      if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia; [exfalso; lia|].
      urun.
      if_cases K2; zify_cond K2; [exfalso; lia|].
      urun.
      if_cases K3; zify_cond K3.
      2:{ exfalso. destruct (sextw_lt (bv_unsigned (sx32 (Z_to_bv 64 (d_tPos d0)))) cap (proj1 TPR) ltac:(lia) K3) as [LT _].
          change (2^32)%Z with 4294967296%Z in LT. rewrite Htp in LT. lia. }
      unfold id in Edb.
      eapply (KEc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] dbytes rest);
        [unfold DSg; dvF_cbn; rewrite Eol0; repeat match goal with |- _ /\ _ => split end; assumption
        | exact DSTA| exact DL| rewrite Edb; reflexivity | ro_close | exact MU | exact WM].
  Qed.

End FNR.
End ACeilS1.
