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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_bzd_frd UKit.
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
  Notation MA := (U0_bzd_frd.MA c). Notation MB := (U0_bzd_frd.MB c). Notation GS := (U0_bzd_frd.GS c).
  Notation R1S := (U0_bzd_frd.R1S c). Notation R2S := (U0_bzd_frd.R2S c). Notation R3S := (U0_bzd_frd.R3S c).
  Notation R4S := (U0_bzd_frd.R4S c). Notation R5S := (U0_bzd_frd.R5S c).

  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & TTA & CRC & RNA & GOT & MI); unfold FGOT in GOT.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & SEP_SD & IAS & IAD & JWF & ENT);
    let OKF' := fresh "OKF" in pose proof OKF as OKF';
    cps_destruct OKF' as (HSM & HTT & SEP_ST & SEP_DT);
    let AL' := fresh "AL" in pose proof AL as AL'; unfold foctx_al, ctx_al in AL';
    cps_destruct AL' as ((ALs & ALsp & ALsrc & ALdst & ALtt & AL16 & AL4) & ALstrm);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & Rcf & Rtt & Rl16 & Rl4);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold FWB in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length (d_tt d0) cap ltac:(lia)) as TTL; pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL; hide_disj.
  Ltac unFI H := cps_destruct H as (Ioc & Iol & Inu & Ik0 & Itp & Irn & Irt & Icb & Iav).
  Ltac ro_close := unfold FROf, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.
  Ltac dsg_close HD NBU MID SM := unfold DSg; focbn; repeat match goal with |- _ /\ _ => split end; [exact_cells HD| exact_cells NBU| exact_cells MID| exact_cells SM].
  Ltac destg_close DSTA DL Edb Lout := unfold DESTg; focbn; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact Lout].
  Ltac goJ HD NBU MID SM DSTA DL Edb Lout MU WM :=
    eapply KJ; [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM
               | unfold ojoin; focbn; repeat match goal with |- _ /\ _ => split end].
  Ltac goE HD NBU MID SM DSTA DL Edb Lout MU WM :=
    eapply KE; [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM
               | unfold oexit; focbn].
  Ltac tt_load i :=
    lazymatch goal with TTA : u32arr _ ?mm TT _ |- _ =>
      let RD := fresh "RD" in
      pose proof (zw32_read s0segs mm TT (d_tt d0) cap i _ TTA ltac:(lia) eq_refl) as RD; wstep; clear RD end.
  Ltac rn_load i :=
    lazymatch goal with RNA : u32arr _ ?mm 0x335b0 rnums_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read s0segs mm 0x335b0 rnums_words i (Z_to_bv 64 (rNums i)) _ RNA (rnums_words_nth i ltac:(lia)) ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite ?(sx32_of_Z (rNums i)) by lia end.
  Ltac goM IHM oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest HD NBU MID SM DSTA DL Edb Lout MU WM :=
    unfold U0_bzd_frd.MA in IHM;
    eapply (IHM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest);
    [ dsg_close HD NBU MID SM | destg_close DSTA DL Edb Lout | ro_close | exact MU | exact WM | | ].
  Ltac start DSm DE ROm FI :=
    let HD := ident:(HD) in let NBU := ident:(NBU) in let MID := ident:(MID) in let SM := ident:(SM) in let Lout := ident:(Lout) in
    unDS DSm; unRO ROm; cps_destruct DE as (DSTA & DL & Edb & Lout); prep; unFI FI;
    unfold DSg in *; focbn_in HD; focbn_in NBU; focbn_in MID; focbn_in SM; focbn_in Lout.
  Ltac cs_split cs w := lazymatch cs with | C4 w :: ?post => constr:((@nil cell, post)) | ?c1 :: ?cs' => let r := cs_split cs' w in lazymatch r with (?pre, ?post) => constr:((c1 :: pre, post)) end end.
  Ltac recell H w v := lazymatch type of H with rw_cells ?sg ?mm ?A ?cs => let r := cs_split cs w in lazymatch r with (?pre, ?post) => apply (C4_recell sg mm A pre w v post) in H; [ cbn [app] in H | ] end end.


  Lemma K_PH_stepM : forall f d s, (1 <= d_out_len d)%Z -> K_PH f d s = K_PM f (pwd d) (pws d s).
  Proof. intros f d s H. rewrite K_PH_step by exact H. cbv zeta. rewrite K_PM_eq. reflexivity. Qed.

  Lemma crc_step_relU : forall crc ch, (0 <= crc < 4294967296)%Z -> (0 <= ch < 256)%Z ->
    (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (sx32 (Z_to_bv 64 (crc32_tbl (Z.lxor (crc / 16777216) ch))))) (crc * 256)))
       mod 4294967296 = crc_update crc ch)%Z.
  Proof.
    intros crc ch Hc Hch.
    pose proof (crc_step_rel (Z_to_bv 64 crc) crc ch ltac:(rewrite unsigned_lit by Lia.lia; apply Z.mod_small; Lia.lia) Hc Hch) as E.
    rewrite (unsigned_lit crc) in E by Lia.lia. rewrite (Z.mod_small (crc * 256) 18446744073709551616) in E by Lia.lia. exact E.
  Qed.

  Lemma fr_A : forall f, MB f -> MA f.
  Proof.
    intros f B. unfold U0_bzd_frd.MA. intros until rest. intros DSm DE ROm MU WM FI Hf.
    pose proof FI as FI0. start DSm DE ROm FI.
    wstep.
    unfold U0_bzd_frd.MB in B.
    eapply (B ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 m oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest);
      [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM| exact FI0| exact Hf].
  Qed.

  Lemma fr_B : forall f, GS f -> MB f.
  Proof.
    intros f G. unfold U0_bzd_frd.MB. intros until m. intros oc ol.
    remember (Z.to_nat ol) as cnt eqn:Hcnt. revert ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 m oc ol Hcnt.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until rest. intros DSm DE ROm MU WM FI Hf.
    start DSm DE ROm FI. focbn_in Edb.
    rewrite K_PM_eq. g8.
    wstep. if_cases K1; zify_cond K1.
    { replace (av =? 0)%Z with true by (symmetry; apply Z.eqb_eq; clear -K1; lia).
      goJ HD NBU MID SM DSTA DL Edb Lout MU WM.
      all: unfold id in Ik0; clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rrnd K1 Rsnb; first [lia | intros; lia]. }
    replace (av =? 0)%Z with false by (symmetry; apply Z.eqb_neq; clear -K1; lia).
    assert (Hav1 : (1 <= av)%Z) by (clear -K1 Iav; lia).
    wstep. wstep. if_cases K2; zify_cond K2.
    { assert (E0 : ol = 0%Z) by (clear -K2 Iol; lia). subst ol.
      rewrite K_PH_0 by (g8; reflexivity).
      unfold U0_bzd_frd.GS in G.
      eapply (G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m oc nu k0 tp rn rt cb out av tout tol toh dbytes rest);
        [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM| | exact Hf| exact Hav1].
      unfold S0F_bzd_fr1.finv; clear -Ioc Inu Ik0 Itp Irn Irt Icb Iav; repeat match goal with |- _ /\ _ => split end; lia. }
    assert (Hol : (1 <= ol)%Z) by (clear -K2 Iol; lia).
    rewrite K_PH_stepM by (g8; lia). g8.
    wstep.
    wstep. notrap.
    wstep.
    cbv beta. rewrite (byte_lit_unsigned oc) by lia.
    pose proof (u8arr_store_ok s0segs _ DST _ (dlen - av) _ DSTA ltac:(lia) eq_refl) as SOK.
    step.
    rewrite BzInv.le1_lit.
    pose proof (u8arr_write s0segs _ DST _ (dlen - av) (Z_to_bv 8 oc) DSTA ltac:(lia)) as DSTB.
    clear DSTA. store_done. try clear SOK. rename DSTB into DSTA.
    pose proof DL as DL'. rewrite <- (upd_length dbytes (Z.to_nat (dlen - av)) (Z_to_bv 8 oc)) in DL'. clear DL.
    destruct rest as [|r0 rest']. { exfalso. pose proof (f_equal (@length byte) Edb) as X. rewrite length_app, length_map, length_rev in X. cbn [length] in X. clear -X DL' Lout Hav1. rewrite upd_length in DL'. lia. }
    rewrite Edb in DSTA. replace (Z.to_nat (dlen - av)) with (length out) in DSTA by (clear -Lout; lia).
    rewrite (dest_snoc out (r0 :: rest') oc r0 rest' eq_refl) in DSTA.
    remember (upd dbytes (Z.to_nat (dlen - av)) (Z_to_bv 8 oc)) as dbytes' eqn:Xdb.
    assert (Edb' : dbytes' = map (Z_to_bv 8) (rev (oc :: out)) ++ rest') by (rewrite Xdb, Edb; replace (Z.to_nat (dlen - av)) with (length out) by (clear -Lout; lia); apply (dest_snoc out (r0 :: rest') oc r0 rest' eq_refl)).
    rewrite <- Edb' in DSTA. clear Xdb Edb. rename Edb' into Edb. rename DL' into DL.
    assert (Lout' : Z.of_nat (length (oc :: out)) = (dlen - (av - 1))%Z) by (cbn [length]; clear -Lout; lia). clear Lout. rename Lout' into Lout.
    wstep.
    wstep.
    cbv beta. rewrite ?(byte_lit_unsigned oc) by lia.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    pose proof (crc_idx_byte cb oc ltac:(lia) ltac:(lia)) as Hidx.
    wstep. notrap.
    wstep.
    pose proof (u32arr_read s0segs _ 209272 crc_words (Z.lxor (cb / 16777216) oc) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD.
    wstep.
    clear RD.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    pose proof (crc_update_range cb oc ltac:(lia)) as Rcb'.
    lazymatch type of MID with context [C4 (Z_to_bv 64 (Z.lxor ?a ?b))] => recell MID (Z_to_bv 64 (Z.lxor a b)) (crc_update cb oc) end.
    2:{ rewrite (Z.mod_small (crc_update cb oc) 4294967296) by exact Rcb'. apply crc_step_relU; lia. }
    set (cb' := crc_update cb oc) in *.
    wstep. notrap.
    wstep.
    wstep.
    wstep. notrap.
    wstep.
    wstep. notrap.
    wstep.
    wstep.
    wstep. notrap.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    if_cases Kt; [clear Kt| clear Kt].
    all: cycle 1.
    1: wstep; wstep; wstep; wstep.
    all: eapply (IH (Z.to_nat (ol - 1)) ltac:(clear -Hol Hcnt; lia) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc (ol - 1)%Z eq_refl nu k0 tp rn rt cb' (oc :: out) (av - 1)%Z (tout + 1)%Z _ _ _ rest');
      [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM| | exact Hf].
    all: unfold S0F_bzd_fr1.finv; clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rcb' Hol Hav1; repeat match goal with |- _ /\ _ => split end; lia.
  Qed.

End FR.
End ACeilS1.
