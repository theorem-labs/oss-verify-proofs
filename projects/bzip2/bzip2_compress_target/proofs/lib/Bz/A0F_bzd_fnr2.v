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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf S0_bzd_out BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit DecCutA A0F_decV A0F_bzdV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0F_bzd_fnr1.
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

Section FNR.
  Variable c : foctx.
  Variable SHS : Z. Variable w0 : word.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation TT := (b_tt (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation uspi := (bv_unsigned (o_SP c)).
  Notation RO := (FROfA DI_A0 c). Notation WB := (FWBA c).
  Hypothesis OK : foctx_okA c AIHI0. Hypothesis OKF : foctx_okFA c AIHI0.
  Hypothesis ANS : sanchor S SHS.
  Hypothesis SH : obz_sh DI_A0 c WB m0.
  Hypothesis KJ : A0_FKjoin c SHS w0 (FROfA DI_A0 c).
  Hypothesis KE : A0_FKexit c SHS w0 (FROfA DI_A0 c).

  Notation KH1 := (K_H1 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KH2 := (K_H2 (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KDR := (K_DR (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation KG := (ucG (d_tt (o_d c)) (100000 * b_n (o_cx c)) (sv_nblock (d_sv (o_d c)) + 1)).
  Notation CC r := (ccommit (o_d c) (o_s c) r).

  Notation FSLc m := (rw_cells a0segs m uspi
    (bzd_slots S SHS w0 (Z_to_bv 64 (SHS + 1)) (Z_to_bv 64 av0) (Z_to_bv 64 (SHS + 7)) (Z_to_bv 64 (SHS + 394)) (Z_to_bv 64 (SHS + -2147450878))
               (Z_to_bv 64 (SHS + 8)) (Z_to_bv 64 (SHS + 136)) (Z_to_bv 64 (SHS + 2)) (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870)))).
  Notation DESTc := (A0F_bzd_fnr1.DESTc c).
  Notation PS := (A0F_bzd_fnr1.PS c SHS w0). Notation QS := (A0F_bzd_fnr1.QS c SHS w0).
  Notation GS := (A0F_bzd_fnr1.GS c SHS w0). Notation H2S := (A0F_bzd_fnr1.H2S c SHS w0).
  Notation H1S := (A0F_bzd_fnr1.H1S c SHS w0). Notation DRS := (A0F_bzd_fnr1.DRS c SHS w0).
  Let fnr_ret := A0F_bzd_fnr1.fnr_ret c SHS w0 OK OKF ANS SH KJ.
  Let fnr_ret2 := A0F_bzd_fnr1.fnr_ret2 c SHS w0 OK OKF ANS SH KJ.
  Let fnr_G := A0F_bzd_fnr1.fnr_G c SHS w0 OK OKF ANS SH KJ KE.
  Let KEc := A0F_bzd_fnr1.KEc c SHS w0 OK KE.

  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & TTA & CRC & RNA & GOT & MI); unfold FGOTA in GOT; a0img.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac unSH := let SHbf := ident:(SHbf) in let SH' := fresh "SH" in pose proof SH as SH';
    cps_destruct SH' as (SHs & SHt & SHd & SHc & SHr & SHbf & _); a0img;
    let OKF' := fresh "OKF" in pose proof OKF as OKF'; specialize (SHbf (proj1 OKF')); clear OKF'.
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & HSP & HAL & SEP_SM & SEP_SD & SEP_MD & IAS & IAM & IAD & HIHI & JWF & ENT);
    let OKF' := fresh "OKF" in pose proof OKF as OKF';
    cps_destruct OKF' as (HSM & HTT & SEP_ST & SEP_MT & SEP_DT & IAT);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & _ & Rtt & _ & _);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold disj, bzd_img_apart in *;
    unfold FWBA, FWB in *; cbn [app] in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length (d_tt d0) cap ltac:(lia)) as TTL; pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL;
    pose proof (proj2 ANS : saddr S SHS) as ANS0;
    hide_disj.
  Ltac ro_close := unfold FROfA, FGOTA; a0img; repeat match goal with |- _ /\ _ => split end; assumption.

  Notation csnb := (Z_to_bv 64 snb). Notation cpp := (Z_to_bv 64 (snb + 1)). Notation cnn := (Z_to_bv 64 (100000 * n)).
  Notation optr av := (Z_to_bv 64 (DST + (dlen - av))).
  Ltac cinv_close := unfold cinv; ccbv; cbn [length]; repeat match goal with |- _ /\ _ => split end; first [lia | mlia].

  (* [comment removed for export] *)
  Ltac dst_write av ch Edb RL :=
    let E' := ident:(E') in let R' := ident:(R') in lazymatch goal with DSTA : u8arr _ _ DST ?bs |- _ =>
      let SOK := fresh "SOK" in
      pose proof (u8arr_store_ok a0segs _ DST _ (dlen - av) _ DSTA ltac:(lia) eq_refl) as SOK;
      wstep; rewrite BzInv.le1_lit;
      let D := fresh "DSTB" in
      pose proof (u8arr_write a0segs _ DST _ (dlen - av) (Z_to_bv 8 ch) DSTA ltac:(lia)) as D;
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
  Ltac crc_step pclw crc ch Hcrc :=
    let Hidx := fresh "Hidx" in
    pose proof (crc_idx_byte crc ch ltac:(lia) ltac:(lia)) as Hidx;
    wstep; wstep; wstep; rewrite Hcrc; wstep; wstep; wstep;
    arun_to pclw;
    lazymatch goal with CRC : u32arr _ ?mm 802816 crc_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read a0segs mm 802816 crc_words (Z.lxor (crc / 16777216) ch) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD;
      wstep; clear RD end.
  Ltac cc1 := lazymatch goal with |- evt _ (o_KQ c (ccommit _ _ (1%Z, ?X))) _ =>
    change (ccommit (o_d c) (o_s c) (1%Z, X)) with (1%Z, o_d c, o_s c) end.
  Ltac fix_optr av :=
    replace (Z_to_bv 64 (DST + (dlen - av) + 1)) with (Z_to_bv 64 (DST + (dlen - (av - 1)))) by (f_equal; lia).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fnr_H2 : forall f cl, GS f (c_write cl) -> H2S f cl.
  Proof.
    intros f cl G. unfold A0F_bzd_fnr1.H2S, A0F_bzd_fnr1.PS. intros until rest. intros DSm DE FSL ROm MU WM CI Hcrc Htp Hf.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep. unSH.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSgA in *. a0img. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM. unfold bzd_slots in FSL. ccbv_in G.
    rewrite K_H2_eq. ccbv.
    wstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq av 0)) by lia.
      wstep. wstep. wstep. wstep.
      enter_with (fnr_ret _ _ _ _ _ _ _ _ _ _ crcw tpw _ _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSgA; a0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold A0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
        | unfold bzd_slots; exact FSL
        | ro_close | exact MU | exact WM
        | unfold cinv; ccbv; lia | ccbv; exact Hcrc | ccbv; exact Htp ].
    - rewrite (proj2 (Z.eqb_neq av 0)) by lia.
      pose proof (u8arr_bound _ _ _ _ DSTA) as DB.
      (* [comment removed for export] *)
      arun_to 0x86bd8%Z. ack_rd (DST + (dlen - av))%Z 1%Z. ack_merge.
      dst_write av ch Edb RL.
      crc_step 0x86c10%Z crc ch Hcrc.
      (* [comment removed for export] *)
      wstep. wstep. wstep. fix_optr av.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with DSTA : u8arr _ _ DST ?db |- _ => lazymatch type of RL with Z.of_nat (length ?r) = _ =>
          pose proof (crc_step_rel crcw crc ch Hcrc ltac:(lia) ltac:(lia)) as Hcrc';
          unfold A0F_bzd_fnr1.GS, A0F_bzd_fnr1.PS in G;
          enter_with (G _ _ _ _ _ _ _ _ _ tpw mm db r);
          [ ccbv; st_eq
          | unfold DSgA; a0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
          | unfold A0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
          | unfold bzd_slots; exact FSL
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
    unfold A0F_bzd_fnr1.DRS, A0F_bzd_fnr1.QS. intros until rest. (intros DSm DE FSL ROm MU WM CI Hcrc Htp Hf; cps_intros (Hl1 & Ha1 & -> & ->)).
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep. unSH.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSgA in *. a0img. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM. unfold bzd_slots in FSL.
    (* [comment removed for export] *)
    wstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      rewrite K_DR_one by (ccbv; lia). rewrite <- K_H2_go by (ccbv; lia).
      wstep. wstep.
      pose proof (H2 (CLOC crc ch len nu k0 tp out av)) as H2c. unfold A0F_bzd_fnr1.H2S, A0F_bzd_fnr1.PS in H2c.
      enter_with (H2c _ _ _ _ _ _ _ _ crcw tpw _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSgA; a0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold A0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
        | unfold bzd_slots; exact FSL
        | ro_close | exact MU | exact WM
        | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp | ccbv; lia ].
    - rewrite K_DR_step by (ccbv; lia). ccbv.
      pose proof (u8arr_bound _ _ _ _ DSTA) as DB.
      (* [comment removed for export] *)
      arun_to 0x86b44%Z. ack_rd (DST + (dlen - av))%Z 1%Z. ack_merge.
      dst_write av ch Edb RL.
      crc_step 0x86b7c%Z crc ch Hcrc.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep. fix_optr av.
      pose proof (crc_step_rel crcw crc ch Hcrc ltac:(lia) ltac:(lia)) as Hcrc'.
      pose proof (crc_update_range crc ch ltac:(lia)) as CR'.
      wstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_eq (av - 1) 0)) by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          lazymatch goal with DSTA : u8arr _ _ DST ?db |- _ => lazymatch type of RL with Z.of_nat (length ?r) = _ =>
            enter_with (fnr_ret2 _ _ _ _ _ _ _ _ _ _ tpw mm _ db r);
            [ ccbv; st_eq
            | unfold DSgA; a0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
            | unfold A0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
            | unfold bzd_slots; exact FSL
            | ro_close | exact MU | exact WM
            | cinv_close | ccbv; exact Hcrc' | ccbv; exact Htp ]
          end end end.
      + rewrite (proj2 (Z.eqb_neq (av - 1) 0)) by lia.
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          lazymatch goal with DSTA : u8arr _ _ DST ?db |- _ => lazymatch type of RL with Z.of_nat (length ?r) = _ =>
            pose proof (IH (Z.to_nat (len - 1)) ltac:(lia) (CLOC (crc_update crc ch) ch (len - 1) nu k0 tp (ch :: out) (av - 1)) ltac:(reflexivity)) as DRc;
            unfold A0F_bzd_fnr1.DRS, A0F_bzd_fnr1.QS in DRc;
            enter_with (DRc _ _ _ _ _ _ _ _ tpw mm db r);
            [ ccbv; st_eq
            | unfold DSgA; a0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
            | unfold A0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
            | unfold bzd_slots; exact FSL
            | ro_close | exact MU | exact WM
            | cinv_close | ccbv; exact Hcrc' | ccbv; exact Htp | ccbv; lia
            | ccbv; repeat match goal with |- _ /\ _ => split end; [lia | lia | reflexivity | reflexivity] ]
          end end end.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fnr_H1 : forall f cl, GS f cl -> DRS f cl -> H1S f cl.
  Proof.
    intros f cl G DR. unfold A0F_bzd_fnr1.H1S, A0F_bzd_fnr1.QS. intros until rest. intros DSm DE FSL ROm MU WM CI Hcrc Htp Hf _.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & RL). prep. unSH.
    cps_destruct CI as (Ccrc & Cch & Clen & Cnu & Ck0 & Ctp & Cav & Cout).
    destruct cl as [crc ch len nu k0 tp out av]. cbn [c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in *.
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ map (Z_to_bv 8) (rev out) ++ rest)) in Edb.
    unfold DSgA in *. a0img. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM. unfold bzd_slots in FSL.
    unfold A0F_bzd_fnr1.GS, A0F_bzd_fnr1.PS in G. unfold A0F_bzd_fnr1.DRS, A0F_bzd_fnr1.QS in DR.
    rewrite K_H1_eq. ccbv.
    (* [comment removed for export] *)
    wstep. if_cases KA; zify_cond KA; rewrite ?signed_lit_small in * by lia.
    - (* [comment removed for export] *)
      replace (0 <? len) with false by (symmetry; apply Z.ltb_ge; lia).
      wstep. wstep. wstep.
      enter_with (G _ _ _ _ _ _ _ _ crcw tpw _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSgA; a0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold A0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
        | unfold bzd_slots; exact FSL
        | ro_close | exact MU | exact WM
        | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp | ccbv; lia ].
    - replace (0 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
      (* [comment removed for export] *)
      wstep. if_cases KB; zify_cond KB.
      + rewrite (proj2 (Z.eqb_eq av 0)) by lia.
        enter_with (fnr_ret _ _ _ _ _ _ _ _ _ _ crcw tpw _ _ dbytes rest);
          [ ccbv; st_eq
          | unfold DSgA; a0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
          | unfold A0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
          | unfold bzd_slots; exact FSL
          | ro_close | exact MU | exact WM
          | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp ].
      + rewrite (proj2 (Z.eqb_neq av 0)) by lia.
        (* [comment removed for export] *)
        wstep. wstep.
        enter_with (DR _ _ _ _ _ _ _ crcw tpw _ dbytes rest);
          [ ccbv; st_eq
          | unfold DSgA; a0img; dvF_cbn; repeat match goal with |- _ /\ _ => split end; assumption
          | unfold A0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact RL]
          | unfold bzd_slots; exact FSL
          | ro_close | exact MU | exact WM
          | cinv_close | ccbv; exact Hcrc | ccbv; exact Htp | ccbv; lia
          | ccbv; repeat match goal with |- _ /\ _ => split end; [lia | lia | reflexivity | reflexivity] ].
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
  (* [comment removed for export] *)
  Theorem A0F_fastnr : forall (t0 t2 a0 a1 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 w32 w104 w112 : word)
      (m : word -> option byte) (dbytes rest : list byte),
    DSgA DI_A0 c m J d0 s0 -> DESTgA DI_A0 c m s0 dbytes rest ->
    rw_cells a0segs m uspi
      (bzd_slots S SHS w0 w32 w104 w112 (Z_to_bv 64 (SHS + -2147450877)) (Z_to_bv 64 (SHS + -2147450878)) (Z_to_bv 64 (SHS + -2147450872))
                 (Z_to_bv 64 (SHS + -2147450873)) (Z_to_bv 64 (SHS + -2147450875)) (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870))) ->
    RO m -> munch WB m0 m -> wmono a0segs m0 m ->
    d_rand d0 = 0%Z ->
    evt a0segs (KQ (unRLE d0 s0))
        (MS (A0RR c SHS (Z_to_bv 64 (SHS + 398)) t0 (Z_to_bv 64 (SHS + -2147450879)) t2 a0 a1 (Z_to_bv 64 (SHS + -2147450486)) a3 a4 a5 a6
                  (Z_to_bv 64 (SHS + -2147450878)) s3 s4 s7 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86a00) fc None m (seg_rom a0segs)).
  Proof.
    intros until rest. intros DSm DE FSL ROm MU WM RD0. unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & Lout). prep. unSH.
    assert (SMF : smallb d0 = false) by (unfold smallb; rewrite Esm, HSM; reflexivity).
    unfold id in NK0.
    assert (RL : Z.of_nat (length rest) = av0).
    { pose proof (f_equal (@length byte) Edb) as X. rewrite length_app, length_map, length_rev in X. lia. }
    change (id (dbytes = map (Z_to_bv 8) (rev (s_out s0)) ++ rest)) in Edb.
    rewrite (unRLE_creg d0 s0 (Z.to_nat (PP + 2 - d_nused d0)) SMF RD0) by lia.
    cps_destruct (fnr_knot (Z.to_nat (PP + 2 - d_nused d0))) as (_ & _ & _ & H1).
    remember (Z.to_nat (PP + 2 - d_nused d0)) as f eqn:Hf.
    unfold blk_cap.
    unfold DSgA in *. a0img. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM. rewrite Eol0 in HD. unfold bzd_slots in FSL.
    pose proof (word_urange (sx32 (Z_to_bv 64 (d_tPos d0)))) as TPR.
    pose proof (sx32_mod32 (d_tPos d0) ltac:(lia)) as Htp.
    arun_to 0x86b28%Z.
    rewrite En. replace (Z_to_bv 64 (n * 100000)) with (Z_to_bv 64 (100000 * n)) by (f_equal; lia).
    replace (bv_unsigned (Z_to_bv 8 (d_out_ch d0))) with (d_out_ch d0)
      by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; cbn; lia).
    destruct NK0 as [[Hnu Hk0]|[Hnu Htp0]].
    - (* [comment removed for export] *)
      try rewrite (sx32_of_Z (d_k0 d0)) by lia.
      unfold A0F_bzd_fnr1.H1S, A0F_bzd_fnr1.QS in H1.
      enter_with (H1 (c0_of d0 s0) _ _ _ _ _ _ _ (sx32 (Z_to_bv 64 (d_cbcrc d0))) (sx32 (Z_to_bv 64 (d_tPos d0))) _ dbytes rest);
        [ ccbv; st_eq
        | unfold DSgA; a0img; dvF_cbn; rewrite Eol0; repeat match goal with |- _ /\ _ => split end; assumption
        | unfold A0F_bzd_fnr1.DESTc; ccbv; repeat match goal with |- _ /\ _ => split end;
            [exact DSTA| exact DL| unfold id in Edb; rewrite Edb; reflexivity| exact RL]
        | unfold bzd_slots; assumption
        | ro_close | exact MU | exact WM
        | cinv_close | ccbv; apply sx32_mod32; lia | ccbv; exact Htp | ccbv; lia | exact I ].
    - (* [comment removed for export] *)
      rewrite K_H1_eq. ccbv. rewrite Eol0. replace (0 <? 0)%Z with false by reflexivity. cbv beta iota.
      rewrite ucG_go by (ccbv; lia). rewrite G1_None by (ccbv; lia). cc1.
      (* [comment removed for export] *)
      wstep. if_cases KA; zify_cond KA; rewrite ?signed_lit_small in * by lia; [| exfalso; lia].
      wstep. wstep. wstep. wstep.
      wstep. if_cases K1; zify_cond K1; rewrite ?signed_lit_small in K1 by lia; [|exfalso; lia].
      wstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      wstep. wstep. if_cases K3; zify_cond K3.
      { exfalso. destruct (sextw_lt (bv_unsigned (sx32 (Z_to_bv 64 (d_tPos d0)))) cap (proj1 TPR) ltac:(lia) K3) as [LT _].
          change (2^32)%Z with 4294967296%Z in LT. rewrite Htp in LT. lia. }
      wstep.
      unfold id in Edb.
      eapply (KEc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] dbytes rest);
        [unfold DSgA; a0img; dvF_cbn; rewrite Eol0; repeat match goal with |- _ /\ _ => split end; assumption
        | exact DSTA| exact DL| rewrite Edb; reflexivity | unfold bzd_slots; assumption | ro_close | exact MU | exact WM].
  Time Qed.
End FNR.
End ACeilS1.
